import Palamedes.Synthesizer
import Palamedes.Examples.STLC.Predicates
import Mathlib.Tactic.CongrExclamation

open Gen CorrectGen

set_option maxHeartbeats 5000000

def genWellTyped (Γ : List Ty) : Gen Term := by
  -- generator_search (λ t => wellTyped Γ t = true)
  let cg : CorrectGen (λ (t : Term) => wellTyped Γ t = true) := by
    apply convert (by
      funext
      simp [Option.isSome_iff_exists]
      apply exists_congr; intro; rw [true_and]) (s_bind _ _)
    . apply s_arbTy
    . intro
      apply convert (by
        funext
        simp [guard, *]
        conv => rhs; lhs; fun; apply (Term.coerce_to_fold (by aesop) (by aesop) (by intros; simp; rflm) (by intros; simp; rflm))
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
            unfold getType.match_1
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
            conv =>
              -- rhs; apply congrArg; intro; apply congrArg; intro; lhs; lhs; apply (Ty.coerce_match (by aesop) (by aesop))
            unfold getType.match_1
            simp_all [Ty.deforest_eq, Ty.as_or, Option.bind_eq_some]
            rw [exists_comm]
            apply exists_congr; intro; rw [true_and]
            ) (s_bind _ _)
            . cgenerator_search
            . cgenerator_search
  let g : Gen (Term) := by
    optimize_gen cg.val
  have : support cg.val = support g := by
    optimality
  have : Gen.total g := by
    totality
  exact g
