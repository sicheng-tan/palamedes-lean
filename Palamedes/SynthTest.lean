import Palamedes.Free
import Palamedes.Support
import Palamedes.Util

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

theorem decidable_or
    {P : Prop}
    {Q : Prop}
    {R : Prop}
    {b : Decidable P} :
    (Decidable.rec (λ _ => Q) (λ _ => R) b : Prop) ↔ ¬P ∧ Q ∨ P ∧ R := by
  match b with
  | isFalse h => simp_all
  | isTrue h => simp_all

theorem ListF_or
    {α β : Type}
    {P : Prop}
    {Q : α → β → Prop}
    {t : ListF α β} :
    ListF.rec P Q t ↔ (P ∧ t = .nil) ∨ (∃ x b, t = .cons x b ∧ Q x b) := by
  match t with
  | .nil => simp
  | .cons x b => aesop

abbrev synth_pure
  (v' : α) :
  CGen (λ v => v = v') := by
  exists (pure v')
  simp

abbrev synth_pure'
  (v' : α) :
  CGen (λ v => v' = v) := by
  exists (pure v')
  simp_all [Eq.comm]

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

abbrev synth_tuple
    {P : α → Prop}
    {Q : α → β → Prop}
    {R : α × β → Prop}
    {h : ∀ p, P p.fst ∧ Q p.fst p.snd ↔ R p}
    (gx : CGen P)
    (gy : (x : α) → CGen (Q x)) :
    CGen R := by
  have ⟨gx_val, gx_prop⟩ := gx
  exists (do
    let x ← gx_val
    let y ← (gy x).val
    pure (x, y))
  simp_all [-Prod.forall]
  intro ⟨x, y⟩
  have gy_prop := (gy x).property
  simp_all

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
    | .some b' => aesop

abbrev synth_true
    [Arbitrary α] :
    CGen (λ (_ : α) => True) := by
  obtain ⟨g, p⟩ := @Arbitrary.arbitrary α _
  exists g

attribute [simp]
  guard
  failure
  ite
  deforest_decidable_bind
  deforest_decidable_eq
  decidable_or
  ListF_or
attribute [-simp]
  Prod.forall
  CGen
attribute [-aesop]
  Subtype
add_aesop_rules unsafe [
  cases Nat,
  cases Bool,
  apply synth_bind,
  apply synth_bind_arb,
  apply synth_or,
  apply synth_pure,
  apply synth_pure',
  apply synth_true,
  apply synth_tuple,
  apply synth_unfold
]

def genTwo : CGen (λ v => v = 2) := by
  aesop

def genTwo' : CGen (2 = .) := by
  aesop

def genTwoOrThree : CGen (λ v => v = 2 ∨ v = 3) := by
  aesop

def genTwoOrThreeOrFour : CGen (λ v => v = 2 ∨ v = 3 ∨ v = 4) := by
  aesop

def genTwoAndThree : CGen (λ (v : Int × Int) => v.fst = 2 ∧ v.snd = 3) := by
  aesop

def genTwoAndThree' : CGen (λ (v : Int × Int) => v.snd = 3 ∧ v.fst = 2) := by
  aesop

def genAllTwos : CGen (λ v => List.foldrM (λ x () => guard (x == 2)) () v = Option.some ()) := by
  aesop

def genLengthK {k : Nat} :
    @CGen (List Unit) (λ v => List.foldrM (λ _ len_xs => pure (len_xs + 1)) 0 v = Option.some k) := by
  aesop

def genEvenLength :
    @CGen (List Unit) (λ v => List.foldrM (λ _ b => pure (not b)) true v = Option.some true) := by
  aesop

def genEvenLengthTwos :
    @CGen (List Nat) (λ v => List.foldrM (λ x b => do guard (x == 2); pure (not b)) true v = Option.some true) := by
  aesop
