import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Total

namespace Gen

@[reducible]
def arbUnit : Gen Unit := pure ()

namespace CorrectGen

@[reducible]
def carbUnit : @CorrectGen Unit (fun _ => True) :=
  Subtype.mk arbUnit (by simp [arbUnit])

end CorrectGen

namespace Total

-- @[simp]
-- def total_arbUnit : total (arbUnit : Gen Unit) := by
--   simp [arbUnit]

end Total

end Gen
