import Palamedes.Free
import Plausible.Random

def replicateM [Monad m] (n : Nat) (mx : m α) : m (List α) :=
  match n with
  | 0 => pure []
  | n + 1 => do
    let x ← mx
    let xs ← replicateM n mx
    pure (x :: xs)

mutual
partial def sampleSized (n : Nat) (f : Nat → Gen (Option α)) : Plausible.RandT IO α := do
  match (← sampleRand (f n)) with
  | .none => sampleSized (2 * n) f
  | .some v => pure v

partial def sampleRand : Gen α → Plausible.RandT IO α
  | .ret v' => pure v'
  | .choose lo hi pf => Plausible.Random.randBound Nat lo hi pf
  | .sized f => sampleSized 100 f
  | .bind x f => sampleRand x >>= sampleRand ∘ f
end

partial def sample : Gen α → IO α := Plausible.runRand ∘ sampleRand

partial def sampleN (n : Nat) : Gen α → IO (List α) := replicateM n ∘ Plausible.runRand ∘ sampleRand
