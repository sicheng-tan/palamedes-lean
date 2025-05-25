import Palamedes.V2.Gen
import Palamedes.V2.CorrectGen
import Palamedes.V2.Total
import Palamedes.V2.RuleSets
import Palamedes.V2.Optimizer

namespace Gen

def arbBool : Gen Bool := pick (pure true) (pure false)

namespace CorrectGen

@[reducible, aesop unsafe (rule_sets := [synthesis])]
def carbBool : @CorrectGen Bool (fun _ => True) :=
  Subtype.mk arbBool (by simp [arbBool])

end CorrectGen

namespace Total

@[simp]
def total_arb_Bool : total (arbBool : Gen Bool) := by
  simp [arbBool]

end Total

end Gen
