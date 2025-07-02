import Palamedes.Synthesizer

open Gen CorrectGen

namespace SortedBetween

@[simp]
def sortedBetween : List Nat → Nat × Nat → Bool := fun xs (lo, hi) =>
  match xs with
  | [] => true
  | x :: xs' => (lo <= x && x <= hi) && sortedBetween xs' (x, hi)

def genSortedBetween (lo hi : Nat) : Gen (List Nat) := by
  generator_search (fun xs => sortedBetween xs (lo, hi) = true)

end SortedBetween
