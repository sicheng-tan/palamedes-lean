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
    CorrectGen (fun b => ∃ a, P a ∧ Q a b) :=
  Subtype.mk (x.val >>= fun a => (f a).val) <| by
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
    CorrectGen (fun a => P a ∨ Q a) :=
  Subtype.mk (pick x.val y.val) <| by
    simp [x.property, y.property]

@[reducible]
def convert
    (h : P = Q)
    (g : CorrectGen P) :
    CorrectGen Q :=
  Subtype.mk g.val <| by
    simp [h, g.property]

@[reducible]
def s_assume_general
    {P : Bool}
    {Q : α → Prop}
    (h : ∀ v, Q v → P)
    (g : P → CorrectGen (fun v => Q v)):
    CorrectGen (fun v => Q v) :=
  Subtype.mk (assume P (fun hp => (g hp).val)) <| by
    funext v
    simp_all
    apply Iff.intro
    . intro ⟨ hp, hv ⟩
      simp_all [(g hp).property]
    . intro hq
      exists (h v hq)
      simp_all [(g (h v hq)).property]

@[reducible]
def s_assume_and
    {P : Bool}
    {Q : α → Prop}
    (g : CorrectGen (fun v => Q v)) :
    CorrectGen (fun v => P ∧ Q v) :=
  Subtype.mk (assume P (fun h => g.val)) <| by
    funext v
    simp_all [g.property]

@[reducible]
def s_assume
    {P : Bool}
    (x : α)
    (g : α → CorrectGen (fun v => v = x)) :
    CorrectGen (fun v => P ∧ v = x) :=
  Subtype.mk (assume P (fun h => (g x).val)) <| by
    funext v
    simp_all [(g x).property]

@[reducible]
def duncurry
    {F : α × β → Type u} :
    ((a : α) → (b : β) → F (a, b)) → (p : α × β) → F p :=
  fun f p => f p.1 p.2

end CorrectGen

end Gen
