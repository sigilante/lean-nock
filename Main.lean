import Nock.Basic
-- The runtime/prover bridge is `native_decide`-backed, and the Class D oracle
-- is a fueled testing model.  Only the executable imports them; nothing in the
-- proof chain does.
import Nock.RuntimeBridge
import Nock.Oracle
import Nock.Audit
open Nock
open Noun
open Nock.Audit

-- The quarantined bridge is the ONLY place the compiler axioms are tolerated.
-- Audited here rather than in Nock/Audit.lean, so the proof chain never
-- imports RuntimeBridge.
#audit_bridge decGate_eq decBat_eq

-- Subject: [42 99]
def subj : Noun := cell (atom 42) (atom 99)

-- op 1: constant — *[a 1 b] = b
-- *[0   [1 42]]  = 42
#eval nock (atom 0) (op 1 (atom 42))      -- expect: atom 42
-- *[subj [1 0]]  = 0
#eval nock subj     (op 1 (atom 0))       -- expect: atom 0
-- *[subj [1 [7 8]]] = [7 8]
#eval nock subj     (op 1 (cell (atom 7) (atom 8)))  -- expect: cell 7 8

-- op 0: slot — *[a 0 b] = /[b a]
-- *[subj [0 1]] = subj
#eval nock subj (op 0 (atom 1))           -- expect: cell 42 99
-- *[subj [0 2]] = /[2 subj] = 42
#eval nock subj (op 0 (atom 2))           -- expect: atom 42
-- *[subj [0 3]] = /[3 subj] = 99
#eval nock subj (op 0 (atom 3))           -- expect: atom 99

-- op 3: wut — *[a 3 b] = ?*[a b]
-- ?[42 99] = 0 (cell)
#eval nock subj (op 3 (op 0 (atom 1)))    -- expect: atom 0
-- ?42 = 1 (atom)
#eval nock subj (op 3 (op 0 (atom 2)))    -- expect: atom 1

-- op 4: lus — *[a 4 b] = +*[a b]
-- *[subj [4 [0 2]]] = +42 = 43
#eval nock subj (op 4 (op 0 (atom 2)))    -- expect: atom 43

-- op 5: tis — *[a 5 b c] = =[*[a b] *[a c]]
-- =[42 99] = 1 (not equal)
#eval nock subj (op 5 (cell (op 0 (atom 2)) (op 0 (atom 3))))  -- expect: atom 1
-- =[42 42] = 0 (equal)
#eval nock subj (op 5 (cell (op 0 (atom 2)) (op 1 (atom 42)))) -- expect: atom 0

-- auto-cons — *[a [b c] d] = [*[a b c] *[a d]]
-- *[subj [[1 42] [1 99]]] = [42 99]
#eval nock subj (cell (op 1 (atom 42)) (op 1 (atom 99)))  -- expect: cell 42 99

def main : IO Unit := pure ()
