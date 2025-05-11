import Palamedes.Support

/-
Convert a proof that, for some generator g of type Gen α, all the values g
generates satisfy some proposition P into a generator that produces pairs of
values and proofs that those values satisfy P.
-/

def Gen.internalizeProofs
    {α : Type}
    (g : Gen α) :
    Gen {x // x ∈ 〚g〛} :=
  match g with
  | .ret v => .ret ⟨v, by simp⟩
  | .bind x f => do
    bind (Gen.internalizeProofs x) (λ a =>
      (λ ⟨x, h⟩ => ⟨x, by
        simp
        exists a.val
        exact And.intro a.property h
      ⟩) <$> Gen.internalizeProofs (f a))
  | .pick x y =>
    pick
      ((λ ⟨x, h⟩ => ⟨x, by left; assumption⟩) <$> Gen.internalizeProofs x)
      ((λ ⟨x, h⟩ => ⟨x, by right; assumption⟩) <$> Gen.internalizeProofs y)
  | .assume b f =>
    .assume b (λ h =>
      (λ ⟨x, h'⟩ => ⟨x, by simp; exists h⟩) <$> Gen.internalizeProofs (f h))
  | .indexed f =>
    .indexed (λ n =>
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
  | ret v => simp [Gen.internalizeProofs]
  | pick _ _ _ _ => simp_all [Gen.internalizeProofs]
  | bind _ _ _ _ => simp_all [Gen.internalizeProofs]
  | indexed f ihf =>
    intro hf
    have ⟨n, hn⟩ := h
    simp [Gen.internalizeProofs]
    exists n
    exists a
    exists hn
    simp
    apply ihf
    exact hn
  | assume _ _ => simp_all [Gen.internalizeProofs]

def CGen.internalizeProofs
    {α : Type}
    {P : α → Prop}
    (g : @CGen α P) :
    (@CGen {v // P v} (λ v => P (↑v))) :=
  let ⟨g_val, g_property⟩ := g
  let g' := Gen.internalizeProofs g_val
  ⟨bind g' (λ ⟨x, pf⟩ => pure ⟨x, (g_property x).mp pf⟩),
   by
    simp [optBind_bind, bind]
    intro a
    intro pf
    apply Iff.intro
    . intro ⟨x, hx⟩
      apply (g_property a).mp x
    . intro h
      exists (g_property a).mpr h
      simp [g']
      exact injProof_correct ((g_property a).mpr h)⟩
