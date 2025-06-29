import Palamedes.Synthesizer

open Gen CorrectGen

set_option maxHeartbeats 5000000

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

attribute [local simp] Ty.as_or Ty.deforest_eq in
def genWellTyped (Γ : List Ty) : Gen Term := by
  -- generator_search (λ t => wellTyped Γ t = true)
  sorry
