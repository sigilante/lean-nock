import Lean
import Nock.Basic
open Noun

/-! ## Nock bracket-notation macro

    `n! "[8 [1 0] [4 0 6]]"` parses the string at **compile time** and
    elaborates to the corresponding `Noun` term.  The result is fully
    transparent to the Lean kernel, so it can appear in `NockEval`
    propositions, `theorem` statements, and `rfl` proofs, as well as
    `#eval` tests.

    Brackets right-associate: `"[1 2 3]"` → `cell 1 (cell 2 3)`.
-/

private def tokenizeNock (s : String) : List String :=
  s.foldl (fun acc c =>
    if c == '[' || c == ']' then acc ++ " " ++ c.toString ++ " "
    else acc ++ c.toString) ""
  |>.splitOn " " |>.filter (· != "")

private def rightAssoc : List Noun → Option Noun
  | []      => none
  | [x]     => some x
  | x :: xs => (rightAssoc xs).map (Noun.cell x)

mutual

private partial def collectItems (toks : List String) (acc : List Noun) :
    Option (List Noun × List String) :=
  match toks with
  | []        => none            -- unclosed bracket
  | "]" :: r  => some (acc, r)
  | _         =>
    match parseTokens toks with
    | none           => none
    | some (n, rest) => collectItems rest (acc ++ [n])

private partial def parseTokens : List String → Option (Noun × List String)
  | []          => none
  | "[" :: rest =>
    match collectItems rest [] with
    | none               => none
    | some (items, rest) => (rightAssoc items).map (·, rest)
  -- Strip Hoon thousands-separator dots (e.g. "1.953.718.630" → 1953718630)
  | tok :: rest => (tok.replace "." "").toNat?.map (Noun.atom ·, rest)

end

/-- Parse a Nock noun from standard bracket notation.  Returns `none` on
    malformed input (unclosed bracket, non-numeric token, etc.). -/
def parseNock (s : String) : Option Noun :=
  match parseTokens (tokenizeNock s) with
  | some (n, []) => some n
  | _            => none

private partial def nounToTerm : Noun → Lean.MacroM (Lean.TSyntax `term)
  | atom k => do
    let kLit : Lean.TSyntax `num := ⟨Lean.Syntax.mkNumLit (toString k)⟩
    `(Noun.atom $kLit)
  | cell a b => do
    `(Noun.cell $(← nounToTerm a) $(← nounToTerm b))

/-- Nock noun literal (string syntax).

    ```
    n! "[8 [1 0] [4 0 6]]"   -- opcode-9 dec-gate invocation
    n! "42"                   -- bare atom
    n! "[1 2 3 4]"            -- right-associates to [1 [2 [3 4]]]
    ```

    The string is parsed at **compile time**; a malformed string is a
    build error, not a runtime failure. -/
macro "n!" s:str : term => do
  let src := s.getString
  match parseNock src with
  | none      => Lean.Macro.throwError s!"n!: failed to parse Nock notation: '{src}'"
  | some noun => nounToTerm noun

/-- Serialize a `Noun` to standard Nock bracket notation.
    Useful for generating strings to paste into `n!` literals. -/
def Noun.toNockStr : Noun → String
  | atom n   => toString n
  | cell a b => "[" ++ a.toNockStr ++ " " ++ b.toNockStr ++ "]"
