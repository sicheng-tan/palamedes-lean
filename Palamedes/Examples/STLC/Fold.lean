import Palamedes.Synthesizer

open Gen CorrectGen

set_option maxHeartbeats 1000000

namespace WellTypedFold

@[simp]
def getTypeFold : Term → List Ty → Option Ty :=
  Term.fold
    (fun _ => pure .unit)
    (fun n Γ' => Γ'[n]?)
    (fun τ₁ b Γ' => do
      let τ₂ ← b (τ₁ :: Γ')
      pure (.arrow τ₁ τ₂))
    (fun b₁ b₂ Γ' => do
      let τ₄ ← b₁ Γ'
      let τ₃ ← b₂ Γ'
      match τ₄ with
      | .arrow τ₁ τ₂ => do
        guard (τ₁ == τ₃)
        pure τ₂
      | _ => none)

@[simp]
def wellTypedFold (Γ : List Ty) (t : Term) : Prop :=
  ∃ τ, getTypeFold t Γ = some τ

attribute [local simp] Ty.as_or Ty.deforest_eq in
def genWellTypedFold (Γ : List Ty) : Gen Term := by
  generator_search (fun t => wellTypedFold Γ t)

end WellTypedFold
