import Palamedes.Synthesizer
import Palamedes.Examples.Tree.BST.BST

open Gen CorrectGen

set_option palamedes.debug true

namespace AVLFold

@[reducible]
def duncurry
    {F : α × β → Type u} :
    ((a : α) → (b : β) → F (a, b)) → (p : α × β) → F p :=
  fun f p => f p.1 p.2

def splitNat
    (n : Nat)
    (z : (n = 0) → α)
    (s : (n' : Nat) → (n = n' + 1) → α) :
    α :=
  match n with
  | 0 => z rfl
  | n' + 1 => s n' rfl

def support_splitNat_congr
    {z z' : n = 0 → Gen α}
    {s s' : (n' : Nat) → n = n' + 1 → Gen α}
    (hz : ∀ {h}, support (z h) = support (z' h))
    (hz : ∀ {n} {h}, support (s n h) = support (s' n h)) :
    support (splitNat n z s) = support (splitNat n z' s') := by
  aesop (add simp splitNat)

@[reducible]
def s_splitNat
    (n : Nat)
    (gz : (n = 0) → CorrectGen P)
    (gs : (n' : Nat) → (n = n' + 1) → CorrectGen P) :
    CorrectGen P :=
    Subtype.mk
      (splitNat n (fun h => (gz h).val) (fun a b => (gs a b).val)) <| by
    match n with
    | 0 => exact (gz _).property
    | n' + 1 => exact (gs _ _).property

def genAVL (height lo hi : Nat) : Gen (Tree Nat) := by
   -- generator_search (fun t =>
  -- Tree.fold (fun bl x br h => decide (h > 0) && bl (h - 1) && br (h - 1)) (fun h => decide (h ≤ 1)) t height = true ∧
  --   Tree.fold
  --       (fun bl x br bounds =>
  --         match bounds with
  --         | (sl, sr) => decide (sl ≤ x) && decide (x ≤ sr) && bl (sl, x - 1) && br (x + 1, sr))
  --       (fun x => true) t (lo, hi) =
  --     true)
  let cg : CorrectGen (fun (t : Tree Nat) =>
      Tree.fold
          (fun bl x br bounds =>
            match bounds with
            | (sl, sr) => decide (sl ≤ x) && decide (x ≤ sr) && bl (sl, x - 1) && br (x + 1, sr))
          (fun x => true) t (lo, hi) =
        true ∧
        Tree.fold (fun bl x br h => decide (h > 0) && bl (h - 1) && br (h - 1)) (fun h => decide (h ≤ 1)) t height = true) := by
      apply convert (by
        funext
        simp [guard, *]
        rw [← Tree.merge_accuM]
        apply and_congr
        . simp_tree_predicate
        . simp_tree_predicate
        ) (Tree.s_unfold _)
      apply duncurry
      intro
      intro
      apply duncurry
      apply duncurry
      intro
      intro
      intro
      rename_i n; apply s_splitNat n
      . cgenerator_search
      . intro
        intro
        rename_i n _; apply s_splitNat n
        . cgenerator_search
        . intro
          intro
          apply convert (by simp_bind_predicate) (s_bind _ _)
          . cgenerator_search
          . cgenerator_search
  let g : Gen (Tree Nat) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
    apply support_splitNat_congr
    . optimality
    . optimality
      apply support_splitNat_congr
      optimality
  exact g
