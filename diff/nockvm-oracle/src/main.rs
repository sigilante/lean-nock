//! Run `[subject formula]` programs through NockVM, one per stdin line, with no
//! jets warm (pure Nock), and print one verdict per line:
//!
//!   <noun>          the result, fully bracketed binary form `[h t]`
//!   CRASH           deterministic %exit
//!   BUDGET          op budget exhausted (consistent with divergence)
//!   MEME            out of memory
//!   NONDET(<mote>)  any other nondeterministic failure
//!   DET(<mote>)     a deterministic failure other than %exit
//!   SCRY            scry blocked or crashed
//!   PANIC           a Rust panic inside NockVM
//!   PARSE_ERROR     malformed input line
//!
//! The op budget is read from NOCK_OP_BUDGET (default 20_000_000 work items).

use std::io::{self, BufRead, Write};
use std::sync::atomic::{AtomicIsize, Ordering};
use std::sync::Arc;

use either::Either;
use ibig::UBig;
use nockvm::hamt::Hamt;
use nockvm::interpreter::{interpret, Context, Error, Mote, NockCancelToken, Slogger};
use nockvm::jets::cold::Cold;
use nockvm::jets::hot::{Hot, URBIT_HOT_STATE};
use nockvm::jets::warm::Warm;
use nockvm::jets::JetDispatchMode;
use nockvm::mem::{NockStack, NOCK_STACK_SIZE_TINY};
use nockvm::noun::{Atom, Cell, Noun, NounSpace, D};

struct Quiet;
impl Slogger for Quiet {
    fn flog(&mut self, _stack: &mut NockStack, _cord: Noun) {}
    fn slog(&mut self, _stack: &mut NockStack, _pri: u64, _noun: Noun) {}
}

fn context(budget: u64) -> Context {
    let mut stack = NockStack::new(NOCK_STACK_SIZE_TINY, 0);
    let arena = stack.arena().clone();
    let cold = Cold::new(&mut stack);
    let warm = Warm::new(&mut stack); // empty: no jet can fire
    let hot = Hot::init(&mut stack, URBIT_HOT_STATE);
    let cache = Hamt::<Noun>::new(&mut stack);
    let test_jets = Hamt::<()>::new(&mut stack);
    Context {
        stack,
        op_budget: Some(budget),
        jet_dispatch: JetDispatchMode::Exact,
        slogger: Box::pin(Quiet),
        cold,
        warm,
        hot,
        cache,
        scry_stack: D(0),
        trace_info: None,
        running_status: Arc::new(AtomicIsize::new(NockCancelToken::RUNNING_IDLE)),
        test_jets,
        arena,
    }
}

/// noun := decimal | '[' noun noun+ ']'   (brackets right-associate)
fn parse(src: &[u8], pos: &mut usize, stack: &mut NockStack) -> Result<Noun, String> {
    while *pos < src.len() && src[*pos] == b' ' {
        *pos += 1;
    }
    match src.get(*pos) {
        Some(b'[') => {
            *pos += 1;
            let mut items = Vec::new();
            loop {
                while *pos < src.len() && src[*pos] == b' ' {
                    *pos += 1;
                }
                match src.get(*pos) {
                    Some(b']') => {
                        *pos += 1;
                        break;
                    }
                    None => return Err("unterminated [".into()),
                    _ => items.push(parse(src, pos, stack)?),
                }
            }
            if items.len() < 2 {
                return Err("cell needs two elements".into());
            }
            let mut acc = items.pop().unwrap();
            while let Some(h) = items.pop() {
                acc = Cell::new(stack, h, acc).as_noun();
            }
            Ok(acc)
        }
        Some(c) if c.is_ascii_digit() => {
            let start = *pos;
            while *pos < src.len() && src[*pos].is_ascii_digit() {
                *pos += 1;
            }
            let digits = std::str::from_utf8(&src[start..*pos]).unwrap();
            let n: UBig = digits.parse().map_err(|_| format!("bad atom {digits}"))?;
            Ok(Atom::from_ubig(stack, &n).as_noun())
        }
        other => Err(format!("unexpected {:?}", other.map(|c| *c as char))),
    }
}

fn show(n: Noun, space: &NounSpace, stack: &mut NockStack, out: &mut String) {
    match n.as_either_atom_cell() {
        Either::Left(a) => out.push_str(&a.in_space(space).as_ubig(stack).to_string()),
        Either::Right(c) => {
            let c = c.in_space(space);
            let (h, t) = (c.head().noun(), c.tail().noun());
            out.push('[');
            show(h, space, stack, out);
            out.push(' ');
            show(t, space, stack, out);
            out.push(']');
        }
    }
}

fn mote(m: &Mote) -> &'static str {
    match m {
        Mote::Exit => "exit",
        Mote::Fail => "fail",
        Mote::Intr => "intr",
        Mote::Meme => "meme",
        Mote::Jest => "jest",
    }
}

fn run(program: &str, budget: u64) -> String {
    let mut ctx = context(budget);
    let prog = {
        let mut pos = 0;
        let r = parse(program.as_bytes(), &mut pos, &mut ctx.stack);
        match r {
            Ok(n) if pos == program.len() => n,
            Ok(_) => return "PARSE_ERROR".into(),
            Err(_) => return "PARSE_ERROR".into(),
        }
    };
    let space = NounSpace::from_arenas(Some(ctx.stack.arena().clone()), None);
    let (subject, formula) = match prog.as_either_atom_cell() {
        Either::Right(c) => {
            let c = c.in_space(&space);
            (c.head().noun(), c.tail().noun())
        }
        Either::Left(_) => return "PARSE_ERROR".into(),
    };
    ctx.running_status.store(NockCancelToken::RUNNING_IDLE, Ordering::SeqCst);
    let result = interpret(&mut ctx, subject, formula);
    match result {
        Ok(res) => {
            let space = NounSpace::from_arenas(Some(ctx.stack.arena().clone()), None);
            let mut out = String::new();
            show(res, &space, &mut ctx.stack, &mut out);
            out
        }
        Err(Error::Deterministic(Mote::Exit, _)) => "CRASH".into(),
        Err(Error::Deterministic(m, _)) => format!("DET({})", mote(&m)),
        Err(Error::NonDeterministic(Mote::Fail, _)) if ctx.op_budget == Some(0) => "BUDGET".into(),
        Err(Error::NonDeterministic(Mote::Meme, _)) => "MEME".into(),
        Err(Error::NonDeterministic(m, _)) => format!("NONDET({})", mote(&m)),
        Err(Error::ScryBlocked(_)) | Err(Error::ScryCrashed(_)) => "SCRY".into(),
    }
}

fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let budget: u64 = std::env::var("NOCK_OP_BUDGET")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(20_000_000);
    let stdin = io::stdin();
    let mut out = io::stdout().lock();
    for line in stdin.lock().lines() {
        let line = line.expect("stdin");
        let program = line.trim();
        if program.is_empty() {
            continue;
        }
        let verdict = std::panic::catch_unwind(|| run(program, budget))
            .unwrap_or_else(|_| "PANIC".into());
        writeln!(out, "{verdict}").expect("stdout");
    }
}
