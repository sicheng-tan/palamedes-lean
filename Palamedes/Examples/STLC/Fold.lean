import Palamedes.Synthesizer
import Palamedes.Examples.STLC.Predicates
import Mathlib.Tactic.CongrExclamation
import Palamedes.Support -- TODO Remove

open Gen CorrectGen

set_option maxHeartbeats 1000000

attribute [local simp] Ty.as_or Ty.deforest_eq in
def genWellTypedFold (Γ : List Ty) : Gen Term := by
  -- generator_search (fun t => ∃ τ, getTypeFold t Γ = some τ)
  let cg : CorrectGen (fun t => ∃ τ, getTypeFold t Γ = some τ) := by
    apply convert (by norm_for_bind) (s_bind _ _)
    . cgenerator_search
    . intro τ
      apply convert (by norm_for_Term_unfold) (Term.s_unfold _)
      intros b Γ
      apply s_caseTy b
      . cgenerator_search
      . cgenerator_search
  let g : Gen (Term) := by
    optimize_gen cg.val
  have support_eq : support cg.val = support g := by
    optimality
  have : Gen.total g := by
    totality
  exact g
