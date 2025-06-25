import Palamedes.Synthesizer

open Gen CorrectGen

def genTrueFold : Gen (List Nat) := by
  generator_search (fun (xs : List Nat) => List.fold (fun x b => b) true xs = true)

@[simp]
def recTrue : List α → Bool
  | [] => true
  | x :: xs => (fun _ => true) x && recTrue xs

def genTrueRec : Gen (List Nat) := by
  generator_search (fun xs => recTrue xs = true)

-- def genTrue : Gen (List Nat) := by
--   generator_search (fun xs => recTrue xs = true)
