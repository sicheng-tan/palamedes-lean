import Palamedes.Synthesizer

open Gen CorrectGen

namespace WellScopedFold

@[simp]
def isWellScopedFold (varCap : Nat) (t : Term) : Bool :=
  Term.fold (fun _ => true) (fun n s => s < n) (fun _ b s => b (s + 1)) (fun b₁ b₂ s => b₁ s && b₂ s) t varCap

def genWellScopedFold : Gen Term := by
  generator_search (fun t => isWellScopedFold 0 t = true)

end WellScopedFold
