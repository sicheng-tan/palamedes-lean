import Palamedes.Free
import Palamedes.Support
import Palamedes.Util

attribute [simp] guard
attribute [-simp] Prod.forall
attribute [-simp] CGen
attribute [-aesop] Subtype

@[simp]
theorem ListF_nil
    {α β : Type}
    {t : ListF α β} :
    ListF.rec True (λ _ _ => False) t ↔ t = .nil := by
  match t with
  | .nil => simp
  | .cons _ _ => simp

@[simp]
theorem ListF_cons
    {α β : Type}
    {P : α → β → Prop}
    {t : ListF α β} :
    ListF.rec False (λ a b => P a b) t ↔
    ∃ a, ∃ b, t = .cons a b ∧ P a b := by
  match t with
  | .nil => simp
  | .cons a b => aesop

@[aesop 90% apply]
abbrev synth_pure (v' : α) : CGen (λ v => v = v') := by
  exists (pure v')
  simp

@[aesop 50% apply]
abbrev synth_bind
    {P : α → Prop}
    {Q : α → β → Prop}
    (hb : CGen P)
    (hf : (a : α) → CGen (Q a)) :
    CGen (λ v => ∃ a, P a ∧ Q a v) := by
  exists .bind hb.val λ a => (hf a).val
  intro v
  obtain ⟨val, property⟩ := hb
  apply Iff.intro <;>
    (rintro ⟨a, ha⟩; exists a; have := (hf a).property; simp_all only [and_self])

@[aesop 50% apply]
abbrev synth_bind_arb
    [Arbitrary α]
    {Q : α → β → Prop}
    (g : (a : α) → CGen (Q a)) :
    CGen (λ v => ∃ a, Q a v) := by
  obtain ⟨arb_val, arb_property⟩ := @Arbitrary.arbitrary α _
  exists (do let x ← arb_val; (g x).val)
  intro b
  simp_all
  apply Iff.intro
  · rintro ⟨v', hv'⟩
    have := (g v').property
    simp_all
    exists v'
  · rintro ⟨v', hv'⟩
    have := (g v').property
    exists v'
    simp_all

@[aesop 2% apply]
abbrev synth_tuple
    {P : α → Prop}
    {Q : α → β → Prop}
    {R : α × β → Prop}
    {h : ∀ p, P p.fst ∧ Q p.fst p.snd ↔ R p}
    (g : CGen (λ v => ∃ x, P x ∧ ∃ y, Q x y ∧ v = (x, y))) :
    CGen R := by
  exists g.val
  simp_all [g.property, Prod.forall]

@[aesop 2% apply]
abbrev synth_tuple'
    {P : β → Prop}
    {Q : β → α → Prop}
    {R : α × β → Prop}
    {h : ∀ p, P p.snd ∧ Q p.snd p.fst ↔ R p}
    (g : CGen (λ v => ∃ y, P y ∧ ∃ x, Q y x ∧ v = (x, y))) :
    CGen R := by
  exists g.val
  simp_all [g.property, Prod.forall]
  intro a b
  apply Iff.intro
  . rintro ⟨y, hy, x, hx, ha, hb⟩
    subst ha
    subst hb
    exact (h a b).mp (And.intro hy hx)
  . intro hr
    have ⟨hb, ha⟩ := (h a b).mpr hr
    exists b
    apply And.intro hb
    exists a

@[aesop 2% apply]
abbrev synth_tuple_first
    [Arbitrary β]
    {P : α → Prop}
    {R : α × β → Prop}
    {h : ∀ p, P p.fst ↔ R p}
    (g : CGen P) :
    CGen R := by
  obtain ⟨g_val, g_property⟩ := g
  obtain ⟨arb_val, arb_property⟩ := @Arbitrary.arbitrary β _
  exists (do pure (← g_val, ← arb_val))
  intro v
  simp_all only [iff_true, support, true_and]
  obtain ⟨fst, snd⟩ := v
  simp_all only [Prod.mk.injEq, exists_and_left, exists_eq', and_true, exists_eq_right']
  apply Iff.intro
  · intro a
    apply (h (fst, snd)).mp
    simp_all
  · intro a
    apply (h (fst, snd)).mpr
    simp_all

@[aesop 2% apply]
abbrev synth_tuple_second
    [Arbitrary α]
    {P : β → Prop}
    {R : α × β → Prop}
    {h : ∀ p, P p.snd ↔ R p}
    (g : CGen P) :
    CGen R := by
  obtain ⟨arb_val, arb_property⟩ := @Arbitrary.arbitrary α _
  obtain ⟨g_val, g_property⟩ := g
  exists (do pure (← arb_val, ← g_val))
  intro v
  simp_all only [iff_true, support, true_and]
  obtain ⟨fst, snd⟩ := v
  simp_all only [Prod.mk.injEq, exists_eq_right_right', exists_and_left, exists_eq', and_true]
  apply Iff.intro
  · intro a
    apply (h (fst, snd)).mp
    simp_all
  · intro a
    apply (h (fst, snd)).mpr
    simp_all

@[aesop 50% apply]
abbrev synth_or
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

@[aesop 50% apply]
abbrev synth_unfold
    {α β : Type}
    {f : α → β → Option β}
    {b z : β}
    (g : (b : β) → CGen (ListF.rec (b = z) (λ a b' => f a b' = some b))) :
    CGen (λ v => List.foldrM f z v = .some b) := by
  exists .unfoldr (λ b => (g b).val) b
  intro v
  induction v generalizing b with
  | nil =>
    have := (g b).property
    simp_all
    rw [Eq.comm]
  | cons x xs ih =>
    have := (g b).property
    simp_all
    match List.foldrM f z xs with
    | .none => simp_all
    | .some b' => simp_all

@[aesop 50% apply]
abbrev synth_ListF_rec
    {P : Prop}
    {Q : α → β → Prop}
    {h_nil : CGen (λ () => P)}
    {h_cons : CGen (λ (v : α × β) => Q v.fst v.snd)} :
    CGen (ListF.rec P Q) := by
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

@[aesop 50% apply]
abbrev synth_true
    [Arbitrary α] :
    CGen (λ (_ : α) => True) := by
  obtain ⟨g, p⟩ := @Arbitrary.arbitrary α _
  exists g

def genTwo : CGen (λ v => v = 2) := by
  aesop

def genTwo' : CGen (2 = .) := by
  aesop (add simp Eq.comm)

def genTwoOrThree : CGen (λ v => v = 2 ∨ v = 3) := by
  aesop

def genTwoOrThreeOrFour : CGen (λ v => v = 2 ∨ v = 3 ∨ v = 4) := by
  aesop

abbrev genTwoAndThree : CGen (λ (v : Int × Int) => v.fst = 2 ∧ v.snd = 3) := by
  aesop

abbrev genTwoAndThree' : CGen (λ (v : Int × Int) => v.snd = 3 ∧ v.fst = 2) := by
  aesop

def genAllTwos : CGen (λ v => List.foldrM (λ x () => guard (x == 2)) () v = Option.some ()) := by
  aesop

def genLengthK {k : Nat} :
    @CGen (List Unit) (λ v => List.foldrM (λ _ len_xs => pure (len_xs + 1)) 0 v = Option.some k) := by
  aesop (add unsafe cases Nat)

def genEvenLength :
    @CGen (List Unit) (λ v => List.foldrM (λ _ b => pure (not b)) true v = Option.some true) := by
  aesop (add unsafe cases Bool)

@[simp]
theorem deforest_decidable_bind
    {α β : Type}
    {p : Prop}
    {b : Decidable p}
    {f : α → Option β}
    {x : ¬p → Option α}
    {y : p → Option α} :
    (Decidable.rec x y b : Option α).bind f =
      (Decidable.rec (λ h => (x h).bind f) (λ h => ((y h).bind f)) b : Option β) := by
  match b with
  | isFalse h => simp
  | isTrue h => simp

@[simp]
theorem deforest_decidable_eq
    {α : Type}
    {p : Prop}
    {b : Decidable p}
    {a : α}
    {x : ¬p → α}
    {y : p → α} :
    (Decidable.rec x y b : α) = a ↔
      (Decidable.rec (λ h => x h = a) (λ h => y h = a) b : Prop) := by
  match b with
  | isFalse h => simp
  | isTrue h => simp

@[simp]
theorem decidable_false
    {p : Prop}
    {b : Decidable p} :
    (Decidable.rec (λ _ => False) (λ _ => False) b : Prop) ↔ False := by
  match b with
  | isFalse h => simp
  | isTrue h => simp

@[simp]
theorem decidable_true
    {p q : Prop}
    {b : Decidable p} :
    (Decidable.rec (λ _ => False) (λ _ => q) b : Prop) ↔ p ∧ q := by
  match b with
  | isFalse h => simp_all
  | isTrue h => simp_all

attribute [local simp] failure ite in
def genEvenLengthTwos :
    @CGen (List Nat) (λ v => List.foldrM (λ x b => do guard (x == 2); pure (not b)) true v = Option.some true) := by
  apply synth_unfold
  intro b
  match b with
  | true =>
    simp_all
    apply synth_ListF_rec
    . aesop
    . apply synth_tuple
      case g =>
        apply synth_bind
        . apply synth_pure
          exact 2
        . intro x
          apply synth_bind
          . apply synth_pure
          . intro y
            apply synth_pure
      aesop
  | false => aesop
