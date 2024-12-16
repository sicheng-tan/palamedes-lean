import Palamedes.Free

@[simp]
def support_unfoldr (P : β → ListF α β → Prop) (b : β) (xs : List α) : Prop :=
  match xs with
  | [] => P b .nil
  | x :: xs => ∃ b', P b (.cons x b') ∧ support_unfoldr P b' xs

@[simp]
def support_unfoldW
    {α γ : Type}
    {β : α → Type}
    (P : γ → (Σ a : α, β a → γ) → Prop) (b : γ) (f : W β) : Prop :=
  @W.elim _ _ (γ → Prop)
    (λ ⟨a, result⟩ =>
      λ b =>
        ∃ (b' : β a → γ),
        P b ⟨a, b'⟩ ∧ ∀ (c : β a), result c (b' c)) f b

theorem support_unfoldW_valid
    {α β : Type}
    {P : β → ListF α β → Prop}
    {P' : β → (Σ a : Listα α, Listβ α a → β) → Prop}
    {b : β}
    {xs : List α}
    {xs' : W (Listβ α)}
    (hxs : xs' = ofList xs)
    (hP : ∀ b,
      P b .nil = P' b ⟨.nil, Empty.elim⟩ ∧
      ∀ x b', P b (.cons x b') = P' b ⟨.cons x, λ () => b'⟩) :
  support_unfoldr P b xs = support_unfoldW P' b xs' := by
  induction xs generalizing b xs' with
  | nil =>
    simp_all only [eq_iff_iff, support_unfoldr, support_unfoldW]
    apply Iff.intro
    · intro ha
      simp [ofList, W.elim]
      exists Empty.elim
      apply And.intro
      . apply ha
      . intro c
        contradiction
    · intro ha
      simp [W.elim] at ha
      have ⟨b', hb', _⟩ := ha
      conv at hb' =>
        congr
        . skip
        . congr
          intro c'
          tactic => contradiction
      apply hb'
  | cons x xs ih =>
    simp_all [ofList, W.elim]
    apply Iff.intro
    . rintro ⟨b', hb'⟩
      exists λ () => b'
      apply And.intro
      . apply hb'.left
      . intro ()
        exact hb'.right
    . rintro ⟨b', hb'1, hb'2⟩
      exists b' ()
      subst hxs
      simp_all only [and_true]
      exact hb'1

@[simp]
def support : Gen α → α → Prop
  | .ret v' => (. = v')
  | .choose lo hi _ => λ v => lo ≤ v ∧ v ≤ hi
  | .unfoldr f b => support_unfoldr (λ b' => support (f b')) b
  | .unfoldW f b => support_unfoldW (λ b' => support (f b')) b
  | .bind x f => λ v => ∃ v', support x v' ∧ support (f v') v
  | .fail => λ _ => False

@[simp]
abbrev CGen {α : Type} (P : α → Prop) :=
  {g : Gen α // ∀ v, support g v ↔ P v}

@[simp]
abbrev CompleteGen {α : Type} (P : α → Prop) :=
  {g : Gen α // ∀ v, P v → support g v}

@[simp]
abbrev SoundGen {α : Type} (P : α → Prop) :=
  {g : Gen α // ∀ v, support g v → P v}

class Arbitrary (α : Type) where
  arbitrary : @CGen α (λ _ => True)

instance : Arbitrary Unit where
  arbitrary := ⟨pure (), by simp⟩

instance : Arbitrary Bool where
  arbitrary := ⟨
    pick (pure true) (pure false),
    by
      simp
      apply And.intro
      . exists 1
      . exists 0
  ⟩
