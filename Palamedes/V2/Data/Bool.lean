import Palamedes.V2.Gen
import Palamedes.V2.CorrectGen
import Palamedes.V2.Total
import Palamedes.V2.RuleSets
import Palamedes.V2.Optimizer

namespace Gen

def arbBool : Gen Bool := pick (pure true) (pure false)

namespace CorrectGen

@[reducible]
def carbBool : @CorrectGen Bool (fun _ => True) :=
  Subtype.mk arbBool (by simp [arbBool])

end CorrectGen

namespace Total

@[simp]
def total_arb_Bool : total (arbBool : Gen Bool) := by
  simp [arbBool]

end Total

namespace OptGen

@[simp]
def opt_arbBool_self : OptGen (arbBool : Gen Bool) :=
  Subtype.mk (arbBool : Gen Bool) rfl

end OptGen

end Gen

add_aesop_rules unsafe (rule_sets := [synthesis]) [
  (by apply Gen.CorrectGen.carbBool),
]

add_aesop_rules unsafe (rule_sets := [optimization]) [
  (by apply Gen.Gen.OptGen.opt_arbBool_self),
]
