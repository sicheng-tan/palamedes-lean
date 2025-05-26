import Palamedes.V2.Gen
import Palamedes.V2.CorrectGen
import Palamedes.V2.Total
import Palamedes.V2.RuleSets
import Palamedes.V2.Optimizer

namespace Gen

def arbUnit : Gen Unit := pure ()

namespace CorrectGen

@[reducible, aesop unsafe (rule_sets := [synthesis])]
def carbUnit : @CorrectGen Unit (fun _ => True) :=
  Subtype.mk arbUnit (by simp [arbUnit])

end CorrectGen

namespace Total

@[simp]
def total_arb_Unit : total (arbUnit : Gen Unit) := by
  simp [arbUnit]

end Total

end Gen
