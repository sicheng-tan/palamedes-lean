import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Total

section TypeDef

inductive Color where
  | red
  | black
deriving BEq, DecidableEq

end TypeDef

namespace Gen

@[irreducible]
def arbColor : Gen Color := pick (pure .red) (pure .black)

@[simp]
theorem support_arbColor :
    support arbColor = fun _ => True := by
    funext x; cases x <;> simp_all [arbColor]

namespace CorrectGen

def s_arbColor : @CorrectGen Color (fun _ => True) :=
  Subtype.mk arbColor <| by
    funext v
    simp

@[reducible]
def s_caseColor
    (c : Color)
    (gr : (c = .red) → @CorrectGen α P)
    (gb : (c = .black) → @CorrectGen α P) :
    @CorrectGen α P :=
  Subtype.mk (match c with
    | .red => gr (by simp)
    | .black => gb (by simp)) <| by
    split <;> rename_i gr gb
    . simp [(gr _).property]
    . simp [(gb _).property]

end CorrectGen

namespace Total

@[simp, aesop safe (rule_sets := [totality])]
theorem total_arbColor : total (arbColor : Gen Color) := by
  simp [arbColor]

end Total

end Gen
