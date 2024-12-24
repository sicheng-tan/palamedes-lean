import Palamedes.Free

inductive ListF (α β : Type) where
  | nil : ListF α β
  | cons : (a : α) → (b : β) → ListF α β

@[simp]
def support_unfoldr (P : β → ListF α β → Prop) (b : β) (xs : List α) : Prop :=
  match xs with
  | [] => P b .nil
  | x :: xs => ∃ b', P b (.cons x b') ∧ support_unfoldr P b' xs

@[simp]
def support : Gen α → α → Prop
  | .ret v' => (. = v')
  | .choose lo hi _ => λ v => lo ≤ v ∧ v ≤ hi
  | .sized f => λ v => ∃ n, support (f n) (some v)
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
