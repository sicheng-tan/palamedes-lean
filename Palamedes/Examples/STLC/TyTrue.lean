
import Palamedes.Synthesizer

open Gen CorrectGen

/-
This was done before the manual generator was added to the synthesizer, but is
now trivial because of that.
-/

-- def genTrueFold : Gen Ty := by
--   generator_search (fun τ => Ty.fold (fun b₁ b₂ => b₁ && b₂) true τ = true)

-- @[simp]
-- def recTrue : Ty → Bool
--   | .unit => true
--   | .arrow τ₁ τ₂ => recTrue τ₁ && recTrue τ₂

-- def genTrueRec : Gen Ty := by
--   generator_search (fun τ => recTrue τ)

-- set_option palamedes.debug true

-- -- def genTrue : Gen Ty := by
-- --   generator_search true

-- def arbTy := genTrueRec
