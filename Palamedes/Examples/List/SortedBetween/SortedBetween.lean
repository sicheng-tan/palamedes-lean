import Palamedes.Synthesizer

open Gen CorrectGen

@[simp]
def sortedBetweenRec : List Nat → Nat × Nat → Bool := fun xs (lo, hi) =>
  match xs with
  | [] => true
  | x :: xs' => (lo <= x && x <= hi) && sortedBetweenRec xs' (x, hi)

def genSortedBetween (lo hi : Nat) : Gen (List Nat) := by
  generator_search (fun xs => sortedBetweenRec xs (lo, hi) = true)
