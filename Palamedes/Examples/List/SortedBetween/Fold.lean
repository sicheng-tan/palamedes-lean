import Palamedes.Synthesizer

open Gen CorrectGen

namespace SortedBetweenFold

def sortedBetweenFold (lo hi : Nat) (xs : List Nat) : Prop :=
  List.fold (fun x b s => decide (s ≤ x) && decide (x ≤ hi) && b x) (fun _ => true) xs lo

def genSortedBetweenFold (lo hi : Nat) : Gen (List Nat) := by
  generator_search (fun xs => sortedBetweenFold lo hi xs = true)

end SortedBetweenFold
