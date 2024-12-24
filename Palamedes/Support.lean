import Palamedes.Free

@[simp]
def support_unfoldr (P : β → ListF α β → Prop) (b : β) (xs : List α) : Prop :=
  match xs with
  | [] => P b .nil
  | x :: xs => ∃ b', P b (.cons x b') ∧ support_unfoldr P b' xs

@[simp]
def support_unfoldTree (P : β → TreeF α β → Prop) (b : β) (t : Tree α) : Prop :=
  match t with
  | .leaf => P b .leaf
  | .node l x r => ∃ bl br,
    P b (.node bl x br) ∧
    support_unfoldTree P bl l ∧
    support_unfoldTree P br r

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
  | .sized f => λ v => ∃ n, support (f n) (some v)
  | .unfoldr f b => support_unfoldr (λ b' => support (f b')) b
  | .unfoldTree f b => support_unfoldTree (λ b' => support (f b')) b
  | .unfoldW f b => support_unfoldW (λ b' => support (f b')) b
  | .bind x f => λ v => ∃ v', support x v' ∧ support (f v') v

notation v " ∈ 〚" g "〛" => support g v

abbrev CGen {α : Type} (P : α → Prop) :=
  {g : Gen α // ∀ v, support g v ↔ P v}

abbrev CompleteGen {α : Type} (P : α → Prop) :=
  {g : Gen α // ∀ v, P v → support g v}

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

def unfoldr' (n : Nat) (f : β → Gen (ListF α β)) (b : β) : Gen (Option (List α)) :=
  match n with
  | 0 => pure none
  | n + 1 => do
    match (← f b) with
    | .nil => pure (some [])
    | .cons x b' => .map (x :: .) <$> unfoldr' n f b'

theorem support_unfoldr' :
    support (.sized (λ n => unfoldr' n f b)) = support_unfoldr (λ b' => support (f b')) b := by
  funext xs
  induction xs generalizing b with
  | nil =>
    simp_all
    apply Iff.intro
    . intro ⟨n, h⟩
      match n with
      | 0 => simp_all
      | n + 1 =>
        simp_all
        have ⟨v', hv'1, hv'2⟩ := h
        match v' with
        | .nil => simp_all
        | .cons _ _ =>
          simp_all
          have ⟨v'', hv''⟩ := hv'2
          match v'' with
          | .none => simp_all
          | .some [] => simp_all [Option.map]
          | .some (x :: xs) => simp_all
    . intro h
      exists 1
      simp [unfoldr']
      exists .nil
  | cons x xs ih =>
    simp_all
    apply Iff.intro
    . intro ⟨n, h⟩
      match n with
      | 0 => simp_all
      | n + 1 =>
        simp_all
        have ⟨v', hv'1, hv'2⟩ := h
        match v' with
        | .nil => simp_all
        | .cons _ b'' =>
          simp_all
          have ⟨v'', hv''⟩ := hv'2
          match v'' with
          | .none => simp_all
          | .some ys =>
            simp_all
            obtain ⟨hv'', rfl, rfl⟩ := hv''
            exists b''
            apply And.intro hv'1
            apply (@ih b'').mp
            exists n
    . intro ⟨b', hx, hxs⟩
      have ⟨n, h⟩ := ih.mpr hxs
      exists n + 1
      simp_all
      exists ListF.cons x b'
      simp_all
      exists some xs
