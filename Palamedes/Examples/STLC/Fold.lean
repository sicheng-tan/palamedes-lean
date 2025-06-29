import Palamedes.Synthesizer

open Gen CorrectGen

set_option maxHeartbeats 1000000

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

attribute [local simp] Ty.as_or Ty.deforest_eq in
def genWellTypedFold (Γ : List Ty) : Gen Term := by
  generator_search (fun (t : Term) => ∃ τ, getTypeFold t Γ = some τ)
  -- let cg : CorrectGen (fun (t : Term) => ∃ τ, getTypeFold t Γ = some τ) := by
  --   cgenerator_search
  -- let g : Gen Term := by
  --   optimize_gen cg.val
  -- let _ : support cg.val = support g := by
  --   optimality
  -- let _ : Gen.total g := by
  --   totality
  -- exact g
