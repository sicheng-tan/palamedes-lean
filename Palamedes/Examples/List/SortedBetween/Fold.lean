import Palamedes.Synthesizer

open Gen CorrectGen

def genSortedBetweenFold (lo hi : Nat) : Gen (List Nat) := by
  generator_search (fun xs => List.fold (fun x b s => decide (s ≤ x) && decide (x ≤ hi) && b x) (fun x => true) xs lo = true)
