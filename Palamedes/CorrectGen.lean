import Palamedes.Gen

@[reducible]
def CorrectGen (P : α → Prop) := {g : Gen α // g.support = P}

namespace Gen

namespace CorrectGen

@[reducible]
def s_pure
    (a' : α) :
    CorrectGen (fun a => a = a') :=
  Subtype.mk (pure a') <| by
    simp

@[reducible]
def s_bind
    {P : α → Prop}
    {Q : α → β → Prop}
    (x : CorrectGen P)
    (f : (a : α) → CorrectGen (Q a)) :
    CorrectGen (λ b => ∃ a, P a ∧ Q a b) :=
  Subtype.mk (x.val >>= λ a => (f a).val) <| by
    funext b
    simp
    apply Iff.intro <;>
      (intro ⟨a, ha⟩;
       exists a
       simp_all [x.property, (f a).property])

@[reducible]
def s_pick
    {P Q : α → Prop}
    (x : CorrectGen P)
    (y : CorrectGen Q) :
    CorrectGen (λ a => P a ∨ Q a) :=
  Subtype.mk (pick x.val y.val) <| by
    simp [x.property, y.property]

@[reducible]
def convert
    (h : P = Q)
    (g : CorrectGen P) :
    CorrectGen Q :=
  Subtype.mk g.val <| by
    simp [h, g.property]

end CorrectGen

end Gen
