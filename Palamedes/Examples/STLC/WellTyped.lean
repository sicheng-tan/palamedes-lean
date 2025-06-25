import Palamedes.Synthesizer
import Palamedes.Examples.STLC.Context
import Palamedes.Examples.STLC.Predicates

open Gen CorrectGen

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
          . apply convert (by aesop) (s_pure _)
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
  let _ : support cg.val = support g := by
    funext
    unfold cg g
    simp_all
    apply exists_congr
    intros
    apply Iff.of_eq
    apply congrFun
    apply congrFun
    apply congrArg
    funext
    funext
    simp
    apply exists_congr
    intros
    apply and_congr
    . apply or_congr
      . apply and_congr
        . exact Eq.to_iff rfl
        . apply or_congr
          . exact Eq.to_iff rfl
          . aesop
      . apply exists_congr
        intros
        apply exists_congr
        intros
        apply and_congr
        . exact Eq.to_iff rfl
        . aesop
    . exact Eq.to_iff rfl
  let _ : Gen.total g := by
    unfold g
    simp [id]
    apply Total.total_bind
    . totality
    . intros
      apply Total.Term.total_unfold
      intros
      apply Total.total_bind
      . apply Gen.Total.total_Ty_caseTy
        . intro
          apply Total.total_pick
          . totality
          . apply Total.total_dite
            . intros
              apply Total.total_pick
              . apply Total.total_bind
                . apply Total.total_elements
                . totality
              . totality
            . totality
        . intros
          apply Total.total_dite
          . intros
            apply Total.total_pick
            . apply Total.total_bind
              . apply Total.total_elements
              . totality
            . totality
          . totality
      . intro v
        intros
        cases v <;> simp
  exact g
