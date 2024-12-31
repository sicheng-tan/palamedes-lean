import Palamedes.Synth
import Palamedes.Sample
import Palamedes.Tree
import Palamedes.Opt
import Mathlib.Tactic.Convert

syntax "apply_synth_pure": tactic
macro_rules
  | `(tactic| apply_synth_pure) => `(tactic|
    first
      | apply synth_pure
      | (conv in _ = _ => rw [eq_comm]); apply synth_pure)

syntax "apply_synth_bind": tactic
macro_rules
  | `(tactic| apply_synth_bind) => `(tactic|
    first
      | apply synth_bind
      | (conv => congr; intro v; congr; intro x; rw [and_comm]); apply synth_bind
      | (conv => congr; intro v; congr; intro x; rw [true_and]); apply synth_bind)

attribute [simp]
  guard
  failure
  ite -- NOTE This may be a problem
  deforest_decidable_bind
  deforest_decidable_eq
  decidable_or
  ListF_or
  TreeF_or
  fold_foldM
  merge_foldM
attribute [-simp]
  Prod.forall
attribute [-aesop]
  Subtype
add_aesop_rules unsafe [
  apply synth_bind,
  apply synth_bind_arb,
  apply synth_or,
  apply synth_pure,
  apply synth_true,
  apply synth_tuple,
  apply synth_unfoldM,
  apply synth_accuM,
  apply synth_accuTreeM,
  apply synth_between,
  (by (conv => congr; intro v; congr; intro x; rw [and_comm]); apply synth_bind),
  (by (conv => congr; intro v; rw [eq_comm]); apply synth_pure),
]
add_aesop_rules 5% [
  cases Nat,
  cases Bool,
]

def genTwo : CGen (. = 2) := by
  aesop

def genTwo' : CGen (2 = .) := by
  aesop

def genSortedBetween
    (lo hi : Nat) :
    CGen (λ v =>
      List.accuM (λ x _ => x)
                 (λ x () => λ (prev : Nat) => do guard (prev ≤ x ∧ x ≤ hi))
                 (λ _ => pure ())
                 v
                 lo = some ()) := by
  simp
  apply synth_accuM
  intro b s
  simp
  apply synth_or
  · apply synth_pure
  · ((conv => congr; intro v; congr; intro x; rw [and_comm]); apply synth_bind)
    · apply synth_between
    · intro x
      ((conv => congr; intro v; congr; intro x; rw [←true_and]); apply synth_bind)
      intro ()
      apply synth_pure

def genEvenLength [Arbitrary α] :
    CGen (λ (v : List α) => List.foldr (λ _ b => not b) true v) := by
  aesop
