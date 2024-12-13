import Palamedes.Free
import Palamedes.Support

theorem unfoldr_foldrM
    {α β : Type}
    {f : α → β → Option β}
    {f' : β → Gen (ListF α β)}
    {b z : β}
    {xs : List α}
    (h_nil : ∀ a, support (f' a) .nil ↔ a = z)
    (h_cons : ∀ x y a, support (f' a) (.cons x y) ↔ f x y = .some a) :
    (support (.unfoldr f' b) xs ↔ List.foldrM f z xs = .some b) := by
  induction xs generalizing z b with
  | nil =>
    apply Iff.intro <;> intro h
    . simp_all only [support, support_unfoldr, List.foldrM_nil, Option.pure_def]
    . simp_all only [List.foldrM_nil, Option.pure_def, Option.some.injEq, support, support_unfoldr]
  | cons x xs ih =>
    apply Iff.intro
    . rintro ⟨b', hx, hxs⟩
      simp
      rw [←(h_cons _ _ _).mp hx]
      rw [(@ih b' z h_nil).mp hxs]
      simp
    . intro h_foldr
      simp
      match h_match : List.foldrM f z xs with
      | .none =>
        simp at *
        rw [h_match] at h_foldr
        contradiction
      | .some b' =>
        exists b'
        apply And.intro
        . apply (h_cons _ _ _).mpr
          simp at h_foldr
          rw [h_match] at h_foldr
          simp at h_foldr
          exact h_foldr
        . exact (ih h_nil).mpr h_match

@[aesop unsafe apply]
def synth_cut
    {P Q : α → Prop}
    {hequiv : ∀ v, P v ↔ Q v}
    (g : CGen P) :
    CGen Q := by
  obtain ⟨val, property⟩ := g
  exists val
  intro v
  simp_all only

@[aesop safe apply]
def synth_pure {v' : α} : CGen (λ v => v = v') := by
  exists (pure v')
  simp

@[aesop safe apply]
def synth_or
    {P Q : α → Prop}
    (x : CGen P)
    (y : CGen Q) :
    CGen (λ v => P v ∨ Q v) := by
  have ⟨gx, hx⟩ := x
  have ⟨gy, hy⟩ := y
  exists (do
    let b ← choose 0 1
    if b == 0 then gx else gy)
  intro v
  simp
  apply Iff.intro <;> intro h
  . have ⟨v', hv'⟩ := h
    match v' with
    | 0 => left; simp at *; apply (hx _).mp hv'
    | 1 => right; simp at *; apply  (hy _).mp hv'
  . match h with
    | .inl h => exists 0; simp; exact (hx _).mpr h
    | .inr h => exists 1; simp; exact (hy _).mpr h

@[simp]
def ListF.match (f : α → β → γ) (c : γ) : ListF α β → γ
  | .nil => c
  | .cons a b => f a b

@[aesop safe apply]
def synth_unfold
    {α β : Type}
    {f : α → β → Option β}
    {b z : β}
    (g : (b : β) → CGen (ListF.match (λ a b' => f a b' = some b) (b = z))) :
    CGen (λ v => List.foldrM f z v = .some b) := by
  refine ⟨?val, ?pf⟩
  . exact unfoldr (λ b => (g b).val) b
  . intro xs
    apply unfoldr_foldrM
    . intro b'
      have ⟨g, hg⟩ := g b'
      apply hg .nil
    . intro x b' b''
      have ⟨g, hg⟩ := g b''
      apply hg (.cons x b')

def synth_match
    {P : Prop}
    {Q : α → β → Prop}
    {h_nil : CGen (λ () => P)}
    {h_cons : CGen (λ (v : α × β) => Q v.fst v.snd)} :
    CGen (ListF.match Q P) := by
  have ⟨g_nil, h_nil⟩ := h_nil
  have ⟨g_cons, h_cons⟩ := h_cons
  refine ⟨?val, ?pf⟩
  . exact (do
      let b ← choose 0 1
      if b == 0
        then let () ← g_nil
             pure .nil
        else let (a, b') ← g_cons
             pure (.cons a b'))
  . intro v
    match v with
    | .nil =>
      simp [ListF.match]
      apply Iff.intro
      . rintro ⟨v', hv'⟩
        match v' with
        | 0 =>
          simp at hv'
          have ⟨_, hv'⟩ := hv'
          exact (h_nil ()).mp hv'
      . intro h
        exists 0
        simp
        exists ()
        exact (h_nil ()).mpr h
    | .cons a b' =>
      simp [ListF.match]
      apply Iff.intro
      . rintro ⟨v', hv'⟩
        match v' with
        | 1 =>
          simp at hv'
          exact (h_cons _).mp hv'
      . intro h
        exists 1
        simp
        exact (h_cons _).mpr h

@[aesop safe apply]
def synth_tuple
    {P : α → Prop}
    {Q : β → Prop}
    (x : CGen P)
    (y : CGen Q) :
    CGen (λ (v : α × β) => P v.fst ∧ Q v.snd) := by
  have ⟨gx, hgx⟩ := x
  have ⟨gy, hgy⟩ := y
  refine ⟨?val, ?pf⟩
  . exact (do
      let x ← gx
      let y ← gy
      pure (x, y))
  . intro v
    unfold CGen at x
    unfold CGen at y
    simp_all only [support]
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    obtain ⟨fst, snd⟩ := v
    simp_all only [Prod.mk.injEq, exists_eq_right_right']

@[aesop safe apply]
def synth_tuple1
    [Arbitrary β]
    {P : α → Prop}
    (hx : CGen P) :
    CGen (λ (v : α × β) => P v.fst) := by
  have arb := (Arbitrary.arbitrary : @CGen β _)
  conv =>
    congr
    intro v
    rw [←and_true (P v.fst)]
  apply synth_tuple hx arb

@[aesop safe apply]
def synth_tuple2
    [Arbitrary α]
    {Q : β → Prop}
    (hy : CGen Q) :
    CGen (λ (v : α × β) => Q v.snd) := by
  have arb := (Arbitrary.arbitrary : @CGen α _)
  conv =>
    congr
    intro v
    rw [←true_and (Q v.snd)]
  apply synth_tuple arb hy

@[aesop safe apply]
def synth_true [Arbitrary α] :
  @CGen α (λ _ => True) := Arbitrary.arbitrary

@[aesop 10% apply]
def synth_and_true
    {P : α → Prop}
    {g : CGen (λ v => P v ∧ True)} :
    CGen P := by
  conv =>
    congr
    intro v
    rw [←and_true (P v)]
  exact g

@[aesop safe apply]
def synth_true' [Arbitrary α] : {g : Gen α // ∀ v, support g v} := by
  have ⟨val, property⟩ := (Arbitrary.arbitrary : @CGen α _)
  exists val
  intro v
  simp_all only [iff_true]

@[aesop safe apply]
def synth_bind
    {P : α → Prop}
    {Q : α → β → Prop}
    (hb : CGen P)
    (hf : (a : α) → CGen (Q a)) :
    CGen (λ v => ∃ a, P a ∧ Q a v) := by
  exists .bind hb.val λ a => (hf a).val
  intro v
  obtain ⟨val, property⟩ := hb
  apply Iff.intro <;> (rintro ⟨a, ha⟩; exists a; have := (hf a).property; simp_all only [and_self])
