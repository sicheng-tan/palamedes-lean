import Palamedes.Synthesizer

open Gen CorrectGen

@[simp]
def isBST : Tree Nat → (Nat × Nat) → Bool := λ t ⟨lo, hi⟩ =>
  match t with
  | .leaf => true
  | .node l x r =>
    (lo <= x && x <= hi) &&
    isBST l ⟨lo, x - 1⟩ &&
    isBST r ⟨x + 1, hi⟩

-- def genBSTBetweenFold (lo hi : Nat) : Gen (Tree Nat) := by
--   generator_search (fun (t : Tree Nat) =>
--     Tree.fold
--         (fun bl x br s =>
--           match s with
--           | (sl, sr) => (decide (sl ≤ x) && decide (x ≤ sr)) && bl (sl, x - 1) && br (x + 1, sr))
--         (fun _ => true) t (lo, hi) =
--       true)

def genBST (lo hi : Nat) : Gen (Tree Nat) := by
  generator_search (fun t => isBST t (lo, hi))
  -- let cg : CorrectGen (fun t => isBST t (lo, hi)) := by
  --   apply convert (by
  --     funext
  --     simp [guard, *]
  --     conv => rhs; lhs; apply congrFun; apply (Tree.coerce_to_fold (by aesop) (by intros; simp_all; rflm))
  --     rw [← Tree.fold_accu_Option_function_true] <;> try (intros; simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]; aesop) )
  --     (Tree.s_unfold _)
  --   cgenerator_search
  -- let g : Gen (Tree Nat) := by
  --   optimize_gen cg.val
  -- let _ : support cg.val = support g := by
  --   optimality
  -- let _ : total g := by
  --   totality
  -- exact g

/-
def genBST (lo hi : Nat) : Gen (Tree Nat) := by
  let cg : CorrectGen (fun t => isBST t (lo, hi)) := by
    apply convert (by
      funext
      simp [guard, *]
      rw [← Tree.fold_accu_Option_function_true]
      case h t =>
        rw [← Tree.coerce_to_fold] <;> try (intros; simp_all) <;> rflm
      case h t =>
        intros
        simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]
        rfl)
      (Tree.s_unfold _)
    sorry
    --cgenerator_search
  let g : Gen (Tree Nat) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : total g := by
    totality
  exact g-/

/-
TODO:
AVL
CompleteTree
GoodStack
GoodTree
NETree
RBT
STLC


-/
