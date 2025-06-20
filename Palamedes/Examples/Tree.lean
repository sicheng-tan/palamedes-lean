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

-- def isBSTBetween (lo hi : Nat) : Tree Nat → Bool := fun t =>
--   Tree.fold (fun bl x br (sl, sr) => sl ≤ x && x ≤ sr && (bl (lo, x - 1) && br (x + 1, hi) ) ) (fun _ => true) t (lo, hi) = true

set_option palamedes.debug true


def genBSTBetweenFold (lo hi : Nat) : Gen (Tree Nat) := by
  generator_search (fun (t : Tree Nat) =>
    Tree.fold
        (fun bl x br s =>
          match s with
          | (sl, sr) => (decide (sl ≤ x) && decide (x ≤ sr)) && bl (sl, x - 1) && br (x + 1, sr))
        (fun _ => true) t (lo, hi) =
      true) allow_partial -- TODO
  -- let cg : CorrectGen (fun t =>
  --   Tree.fold
  --       (fun bl x br s =>
  --         match s with
  --         | (sl, sr) => (decide (sl ≤ x) && decide (x ≤ sr)) && bl (sl, x - 1) && br (x + 1, sr))
  --       (fun _ => true) t (lo, hi) =
  --     true) := by
  --   -- apply convert (by
  --   --   funext
  --   --   simp [guard, *]
  --   --   rw [← Tree.fold_accu_Option_function_true]
  --   --   intros
  --   --   simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]
  --   --   rfl)
  --   --   (Tree.s_unfold _)
  --   -- intros b s
  --   -- gapply (s_pick _ _)
  --   -- . cgenerator_search
  --   -- . apply (s_bind _ _)
  --   --   . cgenerator_search
  --   --   . cgenerator_search
  --     cgenerator_search
  -- let g : Gen (Tree Nat) := by
  --   optimize_gen cg.val
  -- let _ : support cg.val = support g := by
  --   optimality
  -- exact g


def genBSTBetween (lo hi : Nat) : Gen (Tree Nat) := by
  let cg : CorrectGen (fun t => isBST t (lo, hi)) := by
    apply convert (by
      funext
      simp [guard, *]
      rw [← Tree.fold_accu_Option_function_true]
      case h t =>
        rw [← Tree.coerce_to_fold] --<;> intros <;> simp_all <;> rflm
        . simp_all
        . intros
          simp_all
          rflm
      case h t =>
        intros
        simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff]
        rfl)
      (Tree.s_unfold _)
    intros b s
    gapply (s_pick _ _)
    . cgenerator_search
    . apply (s_bind _ _)
      . cgenerator_search
      . cgenerator_search
  let g : Gen (Tree Nat) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  exact g

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
