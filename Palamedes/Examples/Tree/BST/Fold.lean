import Palamedes.Synthesizer

open Gen CorrectGen

def genBSTFold (lo hi : Nat) : Gen (Tree Nat) := by
  generator_search (fun (t : Tree Nat) =>
    Tree.fold
        (fun bl x br s =>
          match s with
          | (sl, sr) => (decide (sl ≤ x) && decide (x ≤ sr)) && bl (sl, x - 1) && br (x + 1, sr))
        (fun _ => true) t (lo, hi) =
      true)
