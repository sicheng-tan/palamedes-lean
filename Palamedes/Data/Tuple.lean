import Palamedes.Total
import Palamedes.CorrectGen
import Palamedes.Optimizer
import Palamedes.RuleSets

namespace Gen

def tuple
    (x : Gen α)
    (f : α → Gen β) :
    Gen (α × β) := do
  let a ← x
  let b ← f a
  pure (a, b)

namespace CorrectGen

@[reducible, aesop unsafe (rule_sets := [synthesis])]
def ctuple
    {P : α → Prop}
    {Q : α → β → Prop}
    {R : α × β → Prop}
    {h : ∀ v, P v.1 ∧ Q v.1 v.2 ↔ R v}
    (x : CorrectGen P)
    (f : (a : α) → CorrectGen (Q a)) :
    CorrectGen R :=
  Subtype.mk (tuple x.val (fun a => (f a).val)) <| by
    funext (a, b)
    simp_all [x.property, (f a).property, tuple]

end CorrectGen

namespace Total

@[simp]
def total_tuple
    (hx : total x)
    (hy : ∀ {a}, a ∈ 〚x〛 → total (f a)) :
    total (tuple x f) := by
  simp [tuple]
  apply total_bind <;> try assumption
  intro v hv
  simp [hy hv]

end Total

end Gen
