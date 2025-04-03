import Palamedes.Free
import Plausible.Random

def replicateM [Monad m] (n : Nat) (mx : m α) : m (List α) :=
  match n with
  | 0 => pure []
  | n + 1 => do
    let x ← mx
    let xs ← replicateM n mx
    pure (x :: xs)

structure SampleConfig where
  backtrackLimit : Nat
  sizeLimit : Nat
  sizeRetryLimit : Nat

instance : Inhabited SampleConfig where
  default := {backtrackLimit := 100, sizeLimit := 10, sizeRetryLimit := 100}

abbrev SampleM α := ExceptT Unit (Plausible.RandT IO) α

namespace SampleM

def failWith (s : String) : SampleM α := do
  ExceptT.lift (StateT.lift (throw (IO.userError s)))

def next : SampleM Nat := ExceptT.lift Plausible.Rand.next

def randBound (lo hi : Nat) (pf : lo ≤ hi) : SampleM {v : Nat // lo ≤ v ∧ v ≤ hi} := do
  ExceptT.lift (Plausible.Random.randBound Nat lo hi pf)

def weightedChoice (w₁ w₂ : Nat) (g₁ g₂ : SampleM α) : SampleM α := do
  let ⟨b, _⟩ ← SampleM.randBound 0 (w₁ + w₂ - 1) (by simp)
  if b < w₁ then g₁ else g₂

def run : SampleM α → IO α := (. >>= IO.ofExcept) ∘ Plausible.runRand ∘ ExceptT.run

mutual
partial def sizedLoop
    (cfg : SampleConfig)
    (n : Nat)
    (f : Nat → Gen (Option α))
    (remaining : Nat) :
    SampleM α := do
  match (← sampleRand cfg (f n)) with
  | .none =>
    match remaining with
    | 0 => failWith "ran out of fuel"
    | remaining' + 1 => sizedLoop cfg n f remaining'
  | .some v => pure v

partial def backtrackLoop
    (cfg : SampleConfig)
    (w₁ w₂ : Nat)
    (x y : Gen α)
    (remaining : Nat) :
    SampleM α :=
  match remaining with
  | 0 => failWith "backtracked too many times"
  | remaining' + 1 =>
    ExceptT.tryCatch
      (weightedChoice w₁ w₂ (sampleRand cfg x) (sampleRand cfg y))
      (λ () => backtrackLoop cfg w₁ w₂ x y remaining')

partial def sampleRand (cfg : SampleConfig) : Gen α → SampleM α
  | .ret v' => pure v'
  | .gt lo => (· + lo) <$> next
  | .pick (w₁, w₂) x y => backtrackLoop cfg w₁ w₂ x y cfg.backtrackLimit
  | .choose lo hi pf => randBound lo hi pf
  | .sized f => sizedLoop cfg cfg.sizeLimit f cfg.sizeRetryLimit
  | .bind x f => sampleRand cfg x >>= sampleRand cfg ∘ f
  | .guardIn p _ f => if h : p then sampleRand cfg (f h) else throw ()
end

end SampleM

partial def interpGen (cfg : SampleConfig) : Gen α → IO α := SampleM.run ∘ SampleM.sampleRand cfg

partial def sample (g : Gen α) (cfg : SampleConfig := default) : IO α :=
  interpGen cfg g

partial def sampleN (n : Nat) (g : Gen α) (cfg : SampleConfig := default) : IO (List α) :=
  replicateM n <| interpGen cfg g
