import Palamedes.Synthesizer

open Gen CorrectGen

-- def isBST : Tree Nat → (Nat × Nat) → Bool := λ t ⟨lo, hi⟩ =>
--   match t with
--   | .leaf => true
--   | .node l x r =>
--     (lo <= x && x <= hi) &&
--     isBST l ⟨lo, x - 1⟩ &&
--     isBST r ⟨x + 1, hi⟩

-- def isBSTBetween (lo hi : Nat) : Tree Nat → Bool := fun t =>
--   Tree.fold (fun bl x br (sl, sr) => sl ≤ x && x ≤ sr && (bl (lo, x - 1) && br (x + 1, hi) ) ) (fun _ => true) t (lo, hi) = true

def genBSTBetween (lo hi : Nat) : Gen (Tree Nat) :=
  generator_search (fun (t : Tree Nat) =>
    Tree.fold
    (fun bl x br (sl, sr) => sl ≤ x && x ≤ sr && (bl (lo, x - 1) && br (x + 1, hi) ) )
    (fun _ => true)
    t
    (lo, hi) = true)
