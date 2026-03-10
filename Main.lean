import Nock.Basic
open Noun

-- Subject: [42 99]
def subj : Noun := cell (atom 42) (atom 99)

-- *[subj [0 2]] = /[2 subj] = 42
#eval nock subj (op 0 (atom 2))

-- *[subj [0 3]] = /[3 subj] = 99
#eval nock subj (op 0 (atom 3))

-- *[subj [4 [0 2]]] = +(*[subj [0 2]]) = 43
#eval nock subj (op 4 (op 0 (atom 2)))

-- *[subj [5 [0 2] [0 3]]] = =[42 99] = 1
#eval nock subj (op 5 (cell (op 0 (atom 2)) (op 0 (atom 3))))

def main : IO Unit := pure ()
