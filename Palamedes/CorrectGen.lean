import Palamedes.Gen

@[reducible]
def CorrectGen (P : α → Prop) := {g : Gen α // g.support = P}

namespace Gen

@[reducible, simp]
def internalizeProofs
    {α : Type}
    (g : Gen α) :
    Gen {x // x ∈ 〚g〛} :=
  match g with
  | .ret v => pure ⟨v, by simp [Gen.support]⟩
  | .bind x f => do
    internalizeProofs x >>= λ a =>
      (λ ⟨x, h⟩ => ⟨x, by
        simp [Gen.support];
        exists a.val;
        exact And.intro a.property h
      ⟩) <$> internalizeProofs (f a)
  | .pick x y =>
    pick
      ((λ ⟨x, h⟩ => ⟨x, by left; assumption⟩) <$> internalizeProofs x)
      ((λ ⟨x, h⟩ => ⟨x, by right; assumption⟩) <$> internalizeProofs y)
  | .assume b f =>
    assume b (λ h =>
      (λ ⟨x, h'⟩ => ⟨x, by simp [Gen.support]; exists h⟩) <$> internalizeProofs (f h))
  | .indexed f =>
    indexed (λ n =>
      (λ ⟨x, h⟩ =>
        match hx : x with
        | none => none
        | some x' => some ⟨x', by simp [Gen.support]; exists n⟩
      ) <$> internalizeProofs (f n))

namespace CorrectGen

private def injProof_correct :
    a ∈ 〚g〛 →
    ⟨a, h⟩ ∈ 〚internalizeProofs g〛 := by
  intro h
  induction g <;> try simp_all [Gen.support]
  case indexed f ihf =>
    have ⟨n, hn⟩ := h
    exists n
    exists a
    exists hn


@[reducible, simp]
def internalizeProofs
    {α : Type}
    {P : α → Prop}
    (g : @CorrectGen α P) :
    (@CorrectGen {v // P v} (λ v => P (↑v))) :=
  Subtype.mk
    (Gen.internalizeProofs g.val >>=
      (λ ⟨x, pf⟩ => pure ⟨x, by simp [← g.property, pf]⟩)) <| by
    have g_prop := g.property
    simp
    funext a
    simp
    apply Iff.intro
    . simp_all
    . intro h
      exists a.val
      have pf : a.val ∈ 〚g.val〛:= by simp_all
      simp_all [injProof_correct]

notation "↓" x => internalizeProofs x

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
