import Palamedes.Free
import Palamedes.Support

def Gen.internalizeProofs
    {α : Type}
    (g : Gen α) :
    Gen {x // x ∈ 〚g〛} :=
  match g with
  | .ret v => .ret ⟨v, by simp⟩
  | .bind x f => do
    optBind (Gen.internalizeProofs x) (λ a =>
      (λ ⟨x, h⟩ => ⟨x, by
        simp
        exists a.val
        exact And.intro a.property h
      ⟩) <$> Gen.internalizeProofs (f a))
  | .pick w x y =>
    optPick w
      ((λ ⟨x, h⟩ => ⟨x, by left; assumption⟩) <$> Gen.internalizeProofs x)
      ((λ ⟨x, h⟩ => ⟨x, by right; assumption⟩) <$> Gen.internalizeProofs y)
  | .guardIn P d f =>
    .guardIn P d (λ h =>
      (λ ⟨x, h'⟩ => ⟨x, by simp; exists h⟩) <$> Gen.internalizeProofs (f h))
  | .sized f =>
    .sized (λ n =>
      (λ ⟨x, h⟩ =>
        match hx : x with
        | none => none
        | some x' => some ⟨x', by simp; exists n⟩
      ) <$> Gen.internalizeProofs (f n))

attribute [local simp] Functor.map optBind_bind optPick_pick in
def injProof_correct :
    a ∈ 〚g〛 →
    ⟨a, h⟩ ∈ 〚Gen.internalizeProofs g〛 := by
  induction g with
  | ret v => simp
  | pick _ x y ihx ihy => simp_all [Gen.internalizeProofs]
  | bind x f ihx ihf => simp_all [Gen.internalizeProofs]
  | sized f ihf =>
    intro hf
    have ⟨n, hn⟩ := h
    simp
    exists n
    exists a
    exists hn
    simp
    apply ihf
    exact hn
  | guardIn P _ f => simp_all

def CGen.internalizeProofs
    {α : Type}
    {P : α → Prop}
    (g : CGen P) :
    (@CGen {v // P v} (λ v => P (↑v))) :=
  let ⟨g_val, g_property⟩ := g
  let g' := Gen.internalizeProofs g_val
  ⟨optBind g' (λ ⟨x, pf⟩ => pure ⟨x, (g_property x).mp pf⟩),
   by
    simp [optBind_bind]
    intro a
    intro pf
    apply Iff.intro
    . intro ⟨x, hx⟩
      apply (g_property a).mp x
    . intro h
      exists (g_property a).mpr h
      simp [g']
      exact injProof_correct ((g_property a).mpr h)⟩
