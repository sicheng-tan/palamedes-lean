import Palamedes.Free

@[simp]
def support : Gen α → α → Prop
  | .ret v' => (. = v')
  | .choose lo hi _ => λ v => lo ≤ v ∧ v ≤ hi
  | .sized f => λ v => ∃ n, support (f n) (some v)
  | .bind x f => λ v => ∃ v', support x v' ∧ support (f v') v
  | .fail => λ _ => False

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

def arbNat (fuel : Nat) : Gen (Option Nat) :=
  match fuel with
  | 0 => pure none
  | n + 1 =>
    pick (pure (some 0))
         (.map (1 + .) <$> arbNat n)

instance : Arbitrary Nat where
  arbitrary :=  ⟨
      Gen.sized arbNat,
      by
        intro v
        induction v with
        | zero => simp; exists 1; simp; exists 0
        | succ n ih =>
          simp_all
          have ⟨n', hn'⟩ := ih
          exists n' + 1
          simp
          exists 1
          simp
          exists some n
          simp_arith
          assumption
    ⟩
