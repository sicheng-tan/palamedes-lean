import Palamedes.Free
import Plausible.Random

def replicateM [Monad m] (n : Nat) (mx : m α) : m (List α) :=
  match n with
  | 0 => pure []
  | n + 1 => do
    let x ← mx
    let xs ← replicateM n mx
    pure (x :: xs)

abbrev SampleM α := ExceptT Unit (Plausible.RandT IO) α

def SampleM.throwTrueException (s : String) : SampleM α := ExceptT.lift (StateT.lift (throw (IO.userError s)))

def SampleM.next : SampleM Nat := ExceptT.lift Plausible.Rand.next

def SampleM.randBound (lo hi : Nat) (pf : lo ≤ hi) : SampleM {v : Nat // lo ≤ v ∧ v ≤ hi} := do
  ExceptT.lift (Plausible.Random.randBound Nat lo hi pf)

def SampleM.weightedChoice (w₁ w₂ : Nat) (g₁ g₂ : SampleM α) : SampleM α := do
  let ⟨b, _⟩ ← SampleM.randBound 0 (w₁ + w₂ - 1) (by simp)
  if b < w₁ then g₁ else g₂

def SampleM.run : SampleM α → IO α := (. >>= IO.ofExcept) ∘ Plausible.runRand ∘ ExceptT.run

mutual
partial def sizedLoop (n : Nat) (f : Nat → Gen (Option α)) (remaining : Nat) : SampleM α := do
  match (← sampleRand (f n)) with
  | .none =>
    match remaining with
    | 0 => SampleM.throwTrueException "ran out of fuel"
    | remaining' + 1 => sizedLoop n f remaining'
  | .some v => pure v

partial def backtrackLoop (w₁ w₂ : Nat) (x y : Gen α) (remaining : Nat) : SampleM α :=
  match remaining with
  | 0 => SampleM.throwTrueException "backtracked too many times"
  | remaining' + 1 =>
    ExceptT.tryCatch
      (SampleM.weightedChoice w₁ w₂ (sampleRand x) (sampleRand y))
      (λ () => backtrackLoop w₁ w₂ x y remaining')

partial def sampleRand (g : Gen α) (backtrackLimit := 100) (sizeLimit := 10) (sizeRetryLimit := 10) : SampleM α :=
  match g with
  | .ret v' => pure v'
  | .gt lo => do
    let n ← SampleM.next
    pure $ n + lo
  | .pick (w₁, w₂) x y => backtrackLoop w₁ w₂ x y backtrackLimit
  | .choose lo hi pf => SampleM.randBound lo hi pf
  | .sized f => sizedLoop sizeLimit f sizeRetryLimit
  | .bind x f => sampleRand x >>= sampleRand ∘ f
  | .guardIn p _ f => if h : p then sampleRand (f h) else throw ()
end

partial def sample : Gen α → IO α := SampleM.run ∘ sampleRand

partial def sampleN (n : Nat) : Gen α → IO (List α) := replicateM n ∘ SampleM.run ∘ sampleRand
