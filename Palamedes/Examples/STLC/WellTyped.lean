import Palamedes.Synthesizer
import Palamedes.Examples.STLC.TyTrue
import Palamedes.Examples.STLC.Context

open Gen CorrectGen

@[simp]
def getType (Γ : List Ty) : Term → Option Ty
  | .unit => pure .unit
  | .var n => Γ[n]?
  | .abs τ t => .arrow τ <$> getType (τ :: Γ) t
  | .app t1 t2 => do
    match ← getType Γ t1 with
    | .arrow τ1 τ2 => do
      let τ3 ← getType Γ t2
      guard (τ1 == τ3)
      pure τ2
    | .unit => failure

@[simp]
def wellTyped (Γ : List Ty) (t : Term) : Bool :=
  Option.isSome (getType Γ t)

def genWellTyped (Γ : List Ty) : Gen Term := by
  -- generator_search (λ t => wellTyped Γ t)
  sorry
