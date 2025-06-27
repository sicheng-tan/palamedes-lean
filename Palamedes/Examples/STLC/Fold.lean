import Palamedes.Synthesizer
import Palamedes.Examples.STLC.Predicates
import Mathlib.Tactic.CongrExclamation
import Palamedes.Support -- TODO Remove

open Gen CorrectGen

set_option maxHeartbeats 5000000

def genWellTypedFold (Γ : List Ty) : Gen Term := by
  -- generator_search (fun t => ∃ τ, getTypeFold t Γ = some τ)
  let cg : CorrectGen (fun t => ∃ τ, getTypeFold t Γ = some τ) := by
    -- NOTE: Apparently this was causing the kernel panic??? unfold getTypeFold
    gapply (s_bind _ _)
    . cgenerator_search
    . intro τ
      apply convert (by
        funext
        simp [guard, *]
        rw [← Term.fold_accu_Option_function_Option] <;> aesop
        ) (Term.s_unfold _)
      intros b Γ
      apply s_caseTy b
      . intros
        gapply (s_pick _ _)
        . cgenerator_search
        . gapply (s_pick _ _)
          . apply (s_bind _ _)
            . apply (s_indicesOf _ _)
            . cgenerator_search
          . apply convert (by
            funext
            unfold getTypeFold.match_1
            simp_all [Ty.deforest_eq, Ty.as_or, Option.bind_eq_some]
            rw [exists_comm]
            apply exists_congr; intro; rw [true_and]
            ) (s_bind _ _)
            . cgenerator_search
            . cgenerator_search
      . intros
        gapply (s_pick _ _)
        . apply (s_bind _ _)
          . apply (s_indicesOf _ _)
          . cgenerator_search
        . gapply (s_pick _ _)
          . apply convert (by funext; rfl) (s_pure _)
          . apply convert (by
            funext
            unfold getTypeFold.match_1
            simp_all [Ty.deforest_eq, Ty.as_or, Option.bind_eq_some]
            rw [exists_comm]
            apply exists_congr; intro; rw [true_and]
            ) (s_bind _ _)
            . cgenerator_search
            . cgenerator_search
  let g : Gen (Term) := by
    optimize_gen cg.val
  have support_eq : support cg.val = support g := by
    optimality
  have : Gen.total g := by
    totality
  exact g
