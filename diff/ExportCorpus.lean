import Nock.Basic
import Nock.Eval
import Nock.Fuel
import Nock.Comp
import Nock.Term
import Nock.Gate
import Nock.Rec
import Nock.Oracle
open Noun
open Oracle (progs subjects)

/-!
# Differential corpus exporter

Writes lean-nock's compiled formulas, with the verdict lean-nock's own fuel
interpreter `nockF` assigns each, as tab-separated lines on stdout:

    group <TAB> name <TAB> [subject formula] <TAB> expected

`expected` is a noun (fully bracketed binary form), `CRASH` (deterministic
crash), or `TIMEOUT` (no verdict within `fuel` steps, consistent with
divergence).  `diff/run.py` feeds the program column to NockVM and compares.
-/

def show' : Noun → String
  | .atom n => toString n
  | .cell a b => "[" ++ show' a ++ " " ++ show' b ++ "]"

def fuel : Nat := 200000

def verdict (S F : Noun) : String :=
  match nockF fuel S F with
  | some (.val v) => show' v
  | some .exit    => "CRASH"
  | none          => "TIMEOUT"

def line (group name : String) (S F : Noun) : String :=
  s!"{group}\t{name}\t[{show' S} {show' F}]\t{verdict S F}"

-- ── words ──────────────────────────────────────────────────────────────────

def words : List (String × Word) :=
  [("dup", .dup), ("drop", .drop), ("swap", .swap), ("over", .over),
   ("cons", .cons), ("head", .head), ("tail", .tail), ("inc", .inc),
   ("eq", .eq), ("celq", .celq), ("dec", .dec), ("add", .add), ("sub", .sub)]

def leaves : List Noun := [atom 0, atom 1, atom 3, atom 9, cell (atom 1) (atom 2)]

/-- 155 stacks: every leaf, every pair, every triple over `leaves`. -/
def wordSubjects : List Noun :=
  leaves ++
  (leaves.flatMap fun a => leaves.map fun b => cell a b) ++
  (leaves.flatMap fun a => leaves.flatMap fun b => leaves.map fun c => cell a (cell b c))

def wordLines : List String :=
  words.flatMap fun (nm, w) =>
    (wordSubjects.zipIdx).map fun (S, i) => line "word" s!"{nm}#{i}" S (phi w)

-- ── Class D ────────────────────────────────────────────────────────────────

def classdLines : List String :=
  progs.flatMap fun (nm, t) =>
    (subjects.zipIdx).map fun (S, i) => line "classd" s!"{nm}#{i}" S (NT t)

-- ── named definitions ──────────────────────────────────────────────────────

def selfRec : List RTerm := [.ifte (.call 0 .nil) .nil .nil]
def mutualRec : List RTerm := [.ifte (.call 1 .nil) .nil .nil, .ifte (.call 0 .nil) .nil .nil]

/-- Every no-continuation `while` of the Class D corpus, re-encoded as the
    recursive definition `W := p_t · ifte(p_b · W, ε)`. -/
def whileEncodings : List (String × Noun) :=
  progs.filterMap fun (nm, t) =>
    match t with
    | .while tt bb .nil => some (s!"{nm}-as-rec", progF [whileDef tt bb 0] (.call 0 .nil))
    | _ => none

def recLines : List String :=
  let fixed : List (String × Noun) :=
    [("self", progF selfRec (.call 0 .nil)), ("mutual", progF mutualRec (.call 0 .nil))]
  (fixed ++ whileEncodings).flatMap fun (nm, F) =>
    (subjects.zipIdx).map fun (S, i) => line "rec" s!"{nm}#{i}" S F

-- ── gates ──────────────────────────────────────────────────────────────────

def fire : Noun := cell (atom 9) (cell (atom 2) (cell (atom 0) (atom 1)))

/-- Each Class D program packaged as a gate core, sample from the subject
    corpus, fired with `[9 2 0 1]`. -/
def gateLines : List String :=
  progs.flatMap fun (nm, t) =>
    (subjects.zipIdx).map fun (sam, i) =>
      line "gate" s!"{nm}#{i}" (mkGate (gateArm t) sam (atom 0)) fire

-- ── hints ──────────────────────────────────────────────────────────────────

/-- Hint tag 7 is not a hint any runtime interprets, so it exercises the bare
    opcode-11 semantics. -/
def hintLines : List String :=
  let wrap (t : Term) : List (String × Noun) :=
    [("static", cell (atom 11) (cell (atom 7) (NT t))),
     ("dynamic-const", cell (atom 11) (cell (cell (atom 7) (cell (atom 1) (atom 42))) (NT t))),
     ("dynamic-crashclue", cell (atom 11) (cell (cell (atom 7) (cell (atom 0) (atom 0))) (NT t)))]
  (progs.take 6).flatMap fun (nm, t) =>
    (wrap t).flatMap fun (kind, F) =>
      (subjects.zipIdx).map fun (S, i) => line "hint" s!"{nm}-{kind}#{i}" S F

-- ── evaluation-order races ─────────────────────────────────────────────────

def orderLines : List String :=
  let z := cell (atom 0) (atom 0)          -- [0 0]: crashes on any subject
  let L := countUp                          -- diverges on subject 0
  let cases : List (String × Noun) :=
    [("control-crash", z), ("control-diverge", L),
     ("autocons-divL-crashR", cell L z), ("autocons-crashL-divR", cell z L),
     ("op2-divB-crashC", cell (atom 2) (cell L z)), ("op2-crashB-divC", cell (atom 2) (cell z L)),
     ("op5-divB-crashC", cell (atom 5) (cell L z)), ("op5-crashB-divC", cell (atom 5) (cell z L)),
     ("op10-crashPatch-divTree", cell (atom 10) (cell (cell (atom 2) z) L)),
     ("op10-divPatch-crashTree", cell (atom 10) (cell (cell (atom 2) L) z)),
     ("op11-divClue-crashBody", cell (atom 11) (cell (cell (atom 7) L) z)),
     ("op11-crashClue-divBody", cell (atom 11) (cell (cell (atom 7) z) L))]
  cases.map fun (nm, F) => line "order" nm (atom 0) F

-- ── known NockVM divergences (harness sensitivity) ────────────────────────

/-- Opcode-10 edits at an invalid axis.  Nock specifies a deterministic crash;
    NockVM at `73877be2` panics.  Λ never emits these; they are here so the
    harness demonstrably catches a real divergence, and to track the finding. -/
def knownLines : List String :=
  let edit (ax : Nat) (patch : Noun) : Noun :=
    cell (atom 10) (cell (cell (atom ax) (cell (atom 1) patch)) (cell (atom 0) (atom 1)))
  [line "known" "edit-axis0-atom" (atom 42) (edit 0 (atom 99)),
   line "known" "edit-axis0-cell" (cell (atom 1) (atom 2)) (edit 0 (cell (atom 7) (atom 8))),
   line "known" "edit-axis4-into-atom" (cell (atom 1) (atom 2)) (edit 4 (atom 99)),
   line "known" "edit-axis5-into-atom" (cell (atom 1) (atom 2)) (edit 5 (atom 99))]

def main : IO Unit := do
  for l in wordLines ++ classdLines ++ recLines ++ gateLines ++ hintLines ++ orderLines ++ knownLines do
    IO.println l
