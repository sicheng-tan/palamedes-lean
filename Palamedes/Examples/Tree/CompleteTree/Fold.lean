import Palamedes.Synthesizer

open Gen CorrectGen

def genCompleteTreeFold (n : Nat) : Gen (Tree Nat) := by
 -- generator_search (fun t => Tree.fold (fun bl x br s => decide (s > 0) && bl (s - 1) && br (s - 1)) (fun s => s == 0) t n = true)
  sorry
