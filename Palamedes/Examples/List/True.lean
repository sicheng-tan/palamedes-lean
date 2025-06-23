import Palamedes.Synthesizer

open Gen CorrectGen

def genTrueFold : Gen (List Nat) := by
  generator_search (fun (xs : List Nat) => List.fold (fun x b => b) true xs = true)

-- def genTrue : Gen (List Nat) := by
--   generator_search (fun _ => true)
