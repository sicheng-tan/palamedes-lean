import Palamedes.Free

@[simp]
def support_unfoldr (P : β → ListF α β → Prop) (b : β) (xs : List α) : Prop :=
  match xs with
  | [] => P b .nil
  | x :: xs => ∃ b', P b (.cons x b') ∧ support_unfoldr P b' xs

@[simp]
def support : Gen α → α → Prop
  | .ret v' => (. = v')
  | .choose lo hi _ => λ v => lo ≤ v ∧ v ≤ hi
  | .unfoldr f b => support_unfoldr (λ b' => support (f b')) b
  | .bind x f => λ v => ∃ v', support x v' ∧ support (f v') v
  | .fail => λ _ => False

@[simp]
abbrev CGen {α : Type} (P : α → Prop) :=
  {g : Gen α // ∀ v, support g v ↔ P v}

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
