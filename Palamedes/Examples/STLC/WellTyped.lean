import Palamedes.Synthesizer
import Palamedes.Examples.STLC.Context

open Gen CorrectGen

@[simp]
def getType (t : Term) (Γ : List Ty) : Option Ty :=
  match t with
  | .unit => pure .unit
  | .var n => Γ[n]?
  | .abs τ t => do
    let τ' ← getType t (τ :: Γ)
    pure (.arrow τ τ')
  | .app t₁ t₂ => do
    let τ₁ ← getType t₁ Γ
    let τ₂ ← getType t₂ Γ
    match τ₁ with
    | .arrow τarg τres => do
      guard (τarg == τ₂)
      pure τres
    | .unit => failure

@[simp]
def wellTyped (Γ : List Ty) (t : Term) : Bool :=
  Option.isSome (getType t Γ)

@[simp]
def getTypeFold : Term → List Ty → Option Ty :=
  Term.fold
    (λ _ => pure .unit)
    (λ n Γ' => Γ'[n]?)
    (λ τ₁ b Γ' => do
      let τ₂ ← b (τ₁ :: Γ')
      pure (.arrow τ₁ τ₂))
    (λ b₁ b₂ Γ' => do
      let τ₄ ← b₁ Γ'
      let τ₃ ← b₂ Γ'
      match τ₄ with
      | .arrow τ₁ τ₂ => do
        guard (τ₁ == τ₃)
        pure τ₂
      | _ => none)

set_option palamedes.debug true
-- set_option pp.all true

theorem Ty.deforest_eq
    {b b_unit : β}
    {b_arrow : Ty → Ty → β} :
    Ty.rec b_unit (λ τ₁ τ₂ _ _ => b_arrow τ₁ τ₂) τ = b ↔
    Ty.rec (b_unit = b) (λ τ₁ τ₂ _ _ => b_arrow τ₁ τ₂ = b) τ := by
  induction τ <;> aesop

theorem Ty.as_or
  {P_unit : Prop}
  {P_arrow : Ty → Ty → Prop} :
  Ty.rec P_unit (λ τ₁ τ₂ _ _ => P_arrow τ₁ τ₂) τ ↔
  (τ = .unit ∧ P_unit) ∨ (∃ τ₁ τ₂, τ = .arrow τ₁ τ₂ ∧ P_arrow τ₁ τ₂) := by
  induction τ <;> aesop

-- set_option pp.all true

def genWellTypedFold (Γ : List Ty) : Gen Term := by
  -- generator_search (fun t => ∃ τ, getTypeFold t Γ = some τ)
  let cg : CorrectGen (fun t => ∃ τ, getTypeFold t Γ = some τ) := by
    unfold getTypeFold
    gapply (s_bind _ _)
    . cgenerator_search
    . intro τ
      apply convert (by
        funext
        simp [guard, *]
        rw [← Term.fold_accu_Option_function_Option] <;> aesop
        ) (Term.s_unfold _)
      intros b Γ
      apply caseTy b
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
          . apply convert (by aesop) (s_pure _)
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
      . apply Gen.Total.total_Ty_rec
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
      apply caseTy b
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
      . apply Gen.Total.total_Ty_rec
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
