import Palamedes.Synth
import Palamedes.Sample
import Palamedes.Total
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FailIfNoProgress

namespace TotalExperiment

-- Define simplifier tactic that will be used in Aesop rules
macro "simp_palamedes" : tactic =>
  `(tactic|
    simp [
        guard,
        failure,
        ite,
        deforest_decidable_bind,
        deforest_decidable_eq,
        decidable_or,
        ListF_or,
        TreeF_or,
        fold_foldM,
        merge_foldM
      ])

-- Define Aesop rules that should be applied
add_aesop_rules unsafe (rule_sets := [palamedes']) [
  (by apply synth_gt),
  (by apply synth_tuple),
  (by apply synth_conv (by ext; rw [Tree.coerce_to_accuM (by aesop) (by aesop)]) (synth_accuTreeM _)),
  (by apply synth_pure),
  (by first
    | apply synth_or
    | apply synth_conv (by simp_palamedes; exact rfl) (synth_or _ _)),
  (by first
    | apply synth_bind
    | apply synth_conv (by ext; congr!; rw [true_and]) (synth_bind _ _)
    | apply synth_conv (by ext; conv => rhs; congr; intro; rw [and_comm]) (synth_bind _ _)
    | apply synth_conv (by simp_palamedes; exact rfl) (synth_bind _ _)),
  (by apply synth_true),
  (by apply synth_between),
  (by fail_if_no_progress intros),
]

-- Define a tactic for generator synthesis, critically not using Aesop's simplifier or default rules
macro "generator_search" : tactic =>
  `(tactic| aesop (rule_sets := [-default, -builtin, palamedes']) (config := {enableSimp := false}))

-- BST Example
def isBST : Tree Nat → (Nat × Nat) → Bool := λ t ⟨lo, hi⟩ =>
  match t with
  | .leaf => true
  | .node l x r =>
    (lo <= x && x <= hi) &&
    isBST l ⟨lo, x - 1⟩ &&
    isBST r ⟨x + 1, hi⟩

attribute [local simp] isBST in
def genBST (lo hi : Nat) : CGen (λ v => isBST v ⟨lo, hi⟩) := by
  generator_search

-- Define rules for proving totality
add_aesop_rules unsafe (rule_sets := [palamedes_total]) [
  total_optBind,
  total_optPick,
  total_unfoldTree,
  total_choose,
  total_internalizeProofs,
]

add_aesop_rules simp (rule_sets := [palamedes_total]) [
  total,
  pick,
  bind,
  Functor.map,
  CGen.internalizeProofs,
  Gen.internalizeProofs
]

-- Define tactic for proving totality
macro "totality" : tactic =>
  `(tactic| aesop (rule_sets := [palamedes_total]))

example {lo hi : Nat} : total (genBST lo hi).val := by
  unfold genBST
  totality
