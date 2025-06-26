import Palamedes.Synthesizer

open Gen CorrectGen

@[simp]
def recEvenLen : List α → Bool
  | [] => true
  | _ :: xs => !(recEvenLen xs)

def genEvenLenRec : Gen (List Nat) := by
  generator_search (fun (xs : List Nat) => recEvenLen xs = true)

-- def genEvenLen : Gen (List Nat) := by
--   generator_search (fun xs => Nat.mod (List.length xs) 2 == 0)
