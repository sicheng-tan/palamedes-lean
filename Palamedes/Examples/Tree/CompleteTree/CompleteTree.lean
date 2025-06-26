import Palamedes.Synthesizer

open Gen CorrectGen

set_option palamedes.debug true

@[simp]
def isCompleteTree : Tree α → Nat → Bool := λ t n =>
  match t with
  | .leaf => n == 0
  | .node l _ r =>
    n > 0 &&
    isCompleteTree l (n - 1) &&
    isCompleteTree r (n - 1)

def isCompleteTreeFold(t : Tree α) (n : Nat) : Bool :=
  Tree.fold (λ bl _ br s => s > 0 && bl (s - 1) && br (s - 1)) (λ s => s == 0) t n

def genCompleteTreeFold (n : Nat) : Gen (Tree Nat) := by
  -- generator_search (fun t => Tree.fold (fun bl x br s => decide (s > 0) && bl (s - 1) && br (s - 1)) (fun s => s == 0) t n = true)
  let cg : CorrectGen (fun (t : Tree Nat) => Tree.fold (fun bl x br s => decide (s > 0) && bl (s - 1) && br (s - 1)) (fun s => s == 0) t n = true) := by
    apply convert (by
      funext
      simp [guard, *]
      rw [← Tree.fold_accu_Option_function] <;> try aesop) (Tree.s_unfold _)
  let g : Gen (Tree Nat) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g

-- def genCompleteTree (n : Nat) : Gen (Tree Nat) := by
--   generator_search (λ t => isCompleteTree t n = true)
