import Palamedes.Synthesizer

open Gen CorrectGen

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
