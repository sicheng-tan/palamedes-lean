import Palamedes.V2.Gen
import Palamedes.V2.CorrectGen
import Palamedes.V2.Total

namespace Gen

def arbBool : Gen Bool := pick (pure true) (pure false)

namespace CorrectGen

@[reducible]
def carbBool : @CorrectGen Bool (fun _ => True) :=
  Subtype.mk arbBool (by simp [arbBool])

end CorrectGen

namespace Total

@[simp]
def total_arbBool : total (arbBool : Gen Bool) := by
  simp [arbBool]

end Total

end Gen
