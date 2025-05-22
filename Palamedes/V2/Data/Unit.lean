import Palamedes.V2.Gen
import Palamedes.V2.CorrectGen
import Palamedes.V2.Total
import Palamedes.V2.RuleSets
import Palamedes.V2.Optimizer

namespace Gen

def arbUnit : Gen Unit := pure ()

namespace CorrectGen

@[reducible]
def carbUnit : @CorrectGen Unit (fun _ => True) :=
  Subtype.mk arbUnit (by simp [arbUnit])

end CorrectGen

namespace Total

@[simp]
def total_arb_Unit : total (arbUnit : Gen Unit) := by
  simp [arbUnit]

end Total

namespace OptGen

@[simp]
def opt_arbUnit_self : OptGen (arbUnit : Gen Unit) :=
  Subtype.mk (arbUnit : Gen Unit) rfl

end OptGen

end Gen

add_aesop_rules unsafe (rule_sets := [synthesis]) [
  (by apply Gen.CorrectGen.carbUnit),
]

add_aesop_rules unsafe (rule_sets := [optimization]) [
  (by apply Gen.Gen.OptGen.opt_arbUnit_self),
]
