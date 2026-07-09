-- Nock 4K
inductive Noun
  | atom : Nat → Noun
  | cell : Noun → Noun → Noun
  deriving Inhabited, DecidableEq, Repr
open Noun

inductive Loobean
  | true : Loobean  -- 0 in Nock
  | false : Loobean -- 1 in Nock
open Loobean

-- ?[a b]              0
-- ?a                  1
def wut : Noun → Noun
  | atom _ => atom 1
  | cell _ _ => atom 0

/-! ## Primitives

Nock's `+`, `=`, `/`, `#` are partial: they crash on ill-formed arguments.
We model a crash as `none`, never as a panic.  A `panic!` in a proof-facing
definition would reduce to `Inhabited.default = atom 0` inside Lean's logic,
which would let the semantics certify that a crashing computation returns
zero.  The only permitted `panic!` in this file is inside `partial def nock`,
the runtime evaluator, which is never reasoned about. -/

-- +[a b]              +[a b]   (crash)
-- +a                  1 + a
def lusO : Noun → Option Noun
  | atom a   => some (atom (1 + a))
  | cell _ _ => none

-- =[a a]              0
-- =[a b]              1
-- Total: the relation always supplies two nouns, so there is no crash arm.
def tisN (a b : Noun) : Noun := if a = b then atom 0 else atom 1

-- /[1 a]              a
-- /[2 a b]            a
-- /[3 a b]            b
-- /[(a + a) b]        /[2 /[a b]]
-- /[(a + a + 1) b]    /[3 /[a b]]
-- /a                  /a       (crash)
def fasO : Noun → Noun → Option Noun
  | atom 0, _        => none
  | atom 1, a        => some a
  | atom 2, atom _   => none
  | atom 2, cell a _ => some a
  | atom 3, atom _   => none
  | atom 3, cell _ b => some b
  | atom (n + 4), b  =>
      -- /[(2a) b]   = /[2 /[a b]]  recurse first, then take head
      -- /[(2a+1) b] = /[3 /[a b]]  recurse first, then take tail
      match fasO (atom ((n + 4) / 2)) b with
      | some (cell hd tl) => if (n + 4) % 2 = 0 then some hd else some tl
      | some (atom _)     => none
      | none              => none
  | cell _ _, _      => none
termination_by axis _ => match axis with | atom n => n | cell _ _ => 0
decreasing_by omega

-- #[1 a b]            a
-- #[(a + a) b c]      #[a [b /[(a + a + 1) c]] c]
-- #[(a + a + 1) b c]  #[a [/[(a + a) c] b] c]
-- #a                  #a       (crash)
def haxO : Noun → Noun → Noun → Option Noun
  | atom 0, _, _       => none
  | atom 1, a, _       => some a
  | atom (n + 2), b, c =>
      let a : Nat := (n + 2) / 2
      if (n + 2) % 2 = 0 then
        match fasO (atom (a + a + 1)) c with
        | some sib => haxO (atom a) (cell b sib) c
        | none     => none
      else
        match fasO (atom (a + a)) c with
        | some sib => haxO (atom a) (cell sib b) c
        | none     => none
  | cell _ _, _, _     => none
termination_by axis _ _ => match axis with | atom n => n | cell _ _ => 0
decreasing_by all_goals omega

/-! ## Runtime evaluator

`partial def nock` exists for `#eval` and for extracting a working
interpreter.  It is opaque to the kernel and nothing in the proof chain
mentions it.  This is the one place `panic!` is allowed: each call site
that receives `none` from a primitive panics there, rather than the
primitive panicking on its own behalf. -/

mutual
partial def nock : Noun → Noun → Noun
  | _, atom _ => panic! "crash: nock atom formula"
  | a, cell head fol =>
    match head with
    -- *[a [b c] d]        [*[a b c] *[a d]]
    | cell b c =>
      cell (nock a (cell b c)) (nock a fol)
    -- opcodes
    | atom opcode =>
      match opcode with
      -- *[a 0 b]            /[b a]
      | 0 =>
        match fasO fol a with
        | some r => r
        | none   => panic! "crash: fas"
      -- *[a 1 b]            b
      | 1 => fol
      -- *[a 2 b c]          *[*[a b] *[a c]]
      | 2 =>
        match fol with
        | cell b c => nock (nock a b) (nock a c)
        | _ => panic! "crash: invalid formula for opcode 2"
      -- *[a 3 b]            ?*[a b]
      | 3 => wut (nock a fol)
      -- *[a 4 b]            +*[a b]
      | 4 =>
        match lusO (nock a fol) with
        | some r => r
        | none   => panic! "crash: lus on cell"
      -- *[a 5 b c]          =[*[a b] *[a c]]
      | 5 =>
        match fol with
        | cell b c => tisN (nock a b) (nock a c)
        | _ => panic! "crash: invalid formula for opcode 5"
      -- *[a 6 b c d]        *[a *[[c d] 0 *[[2 3] 0 *[a 4 4 b]]]]
      | 6 =>
        match fol with
        | cell b (cell c d) =>
          nock a
            (nock (cell c d)
              (cell (atom 0)
                (nock (cell (atom 2) (atom 3))
                  (cell (atom 0)
                    (nock a (cell (atom 4) (cell (atom 4) b)))))))
        | _ => panic! "crash: invalid formula for opcode 6"
      -- *[a 7 b c]          *[*[a b] c]
      | 7 =>
        match fol with
        | cell b c => nock (nock a b) c
        | _ => panic! "crash: invalid formula for opcode 7"
      -- *[a 8 b c]          *[[*[a b] a] c]
      | 8 =>
        match fol with
        | cell b c => nock (cell (nock a b) a) c
        | _ => panic! "crash: invalid formula for opcode 8"
      -- *[a 9 b c]          *[*[a c] 2 [0 1] 0 b]
      | 9 =>
        match fol with
        | cell b c =>
          nock (nock a c) (cell (atom 2) (cell (cell (atom 0) (atom 1)) (cell (atom 0) b)))
        | _ => panic! "crash: invalid formula for opcode 9"
      -- *[a 10 [b c] d]     #[b *[a c] *[a d]]
      | 10 =>
        match fol with
        | cell (cell b c) d =>
          match haxO b (nock a c) (nock a d) with
          | some r => r
          | none   => panic! "crash: hax"
        | _ => panic! "crash: invalid formula for opcode 10"
      -- *[a 11 [b c] d]     *[[*[a c] *[a d]] 0 3]
      -- *[a 11 b c]         *[a c]
      | 11 =>
        match fol with
        | cell m n =>
          match m with
          | atom _ =>
            let c := n
            nock a c
          | cell _ c =>
            let d := n
            nock (cell (nock a c) (nock a d)) (cell (atom 0) (atom 3))
          -- | _ => panic! "crash: invalid hint form"
        | _ => panic! "crash: invalid formula for opcode 11"
      | _ => panic! "crash: unknown opcode"
end

def op (k : Nat) (arg : Noun) : Noun := cell (atom k) arg
