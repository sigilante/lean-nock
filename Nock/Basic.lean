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

-- +[a b]              +[a b]
-- +a                  1 + a
def lus : Noun → Noun
  | atom a => atom (1 + a)
  | cell _ _ => panic! "crash: lus on cell"

-- =[a a]              0
-- =[a b]              1
def tis : Noun → Noun
  | cell a b => if a = b then atom 0 else atom 1
  | atom _ => panic! "crash: tis on atom"

-- /[1 a]              a
-- /[2 a b]            a
-- /[3 a b]            b
-- /[(a + a) b]        /[2 /[a b]]
-- /[(a + a + 1) b]    /[3 /[a b]]
-- /a                  /a
mutual
def fas : Noun → Noun → Noun
  | atom 0,     _    => panic! "crash: axis 0"
  | atom 1, a        => a
  | atom 2, atom _   => panic! "crash: head of atom"
  | atom 2, cell a _ => a
  | atom 3, atom _   => panic! "crash: tail of atom"
  | atom 3, cell _ b => b
  | atom (n + 4), b =>
    -- /[(2a) b]   = /[2 /[a b]]  recurse first, then take head
    -- /[(2a+1) b] = /[3 /[a b]]  recurse first, then take tail
    let sub : Noun := fas (atom ((n + 4) / 2)) b
    if (n + 4) % 2 = 0 then
      match sub with
      | atom _ => panic! "crash: head of atom"
      | cell hd _ => hd
    else
      match sub with
      | atom _ => panic! "crash: tail of atom"
      | cell _ tl => tl
    | cell _ _,   _    => panic! "crash: axis cell"
termination_by
  axis _ =>
    match axis with
    | atom n => n
    | cell _ _ => 0
end

-- #[1 a b]            a
-- #[(a + a) b c]      #[a [b /[(a + a + 1) c]] c]
-- #[(a + a + 1) b c]  #[a [/[(a + a) c] b] c]
-- #a                  #a
mutual
def hax : Noun → Noun → Noun → Noun
  | atom 0,     _, _ => panic! "crash: hax axis 0"
  | atom 1,     a, _ => a
  | atom (n + 2), b, c =>
    let a : Nat := (n + 2) / 2
    if (n + 2) % 2 = 0 then
      hax (atom a) (cell b (fas (atom (a + a + 1)) c)) c
    else
      hax (atom a) (cell (fas (atom (a + a)) c) b) c
  | cell _ _,   _,   _   => panic! "crash: hax non-atom axis"
termination_by
  axis _ _ =>
    match axis with
    | atom n => n
    | cell _ _ => 0
end

mutual
partial def nock : Noun → Noun → Noun
  | a, atom _ => panic! "crash: nock atom formula"
  | a, cell head fol =>
    match head with
    -- *[a [b c] d]        [*[a b c] *[a d]]
    | cell b c =>
      cell (nock a (cell b c)) (nock a fol)
    -- opcodes
    | atom opcode =>
      match opcode with
      -- *[a 0 b]            /[b a]
      | 0 => fas fol a
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
      | 4 => lus (nock a fol)
      -- *[a 5 b c]          =[*[a b] *[a c]]
      | 5 =>
        match fol with
        | cell b c => tis (cell (nock a b) (nock a c))
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
          hax b (nock a c) (nock a d)
        | _ => panic! "crash: invalid formula for opcode 10"
      -- *[a 11 [b c] d]     *[[*[a c] *[a d]] 0 3]
      -- *[a 11 b c]         *[a c]
      | 11 =>
        match fol with
        | cell m n =>
          match m with
          | atom b =>
            let c := n
            nock a c
          | cell b c =>
            let d := n
            nock (cell (nock a c) (nock a d)) (cell (atom 0) (atom 3))
          -- | _ => panic! "crash: invalid hint form"
        | _ => panic! "crash: invalid formula for opcode 11"
      | _ => panic! "crash: unknown opcode"
    -- | _ => panic! "crash: non-atom opcode"
end

def op (k : Nat) (arg : Noun) : Noun := cell (atom k) arg
