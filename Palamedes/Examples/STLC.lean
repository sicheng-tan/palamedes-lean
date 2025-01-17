import Palamedes.Synth

inductive Ty : Type where
  | unit
  | arrow (τ₁ τ₂ : Ty)
  deriving BEq

def genTy : Nat → Gen (Option Ty)
  | 0 => pure none
  | n + 1 => pick
    (pure (pure .unit))
    (do
      let g1 ← genTy n
      let g2 ← genTy n
      pure (.arrow <$> g1 <*> g2))

theorem genTy_monotonic
    {hlt : n ≤ m}
    (hn : some v ∈ 〚genTy n〛) :
    some v ∈ 〚genTy m〛:= by
  induction m generalizing n with
  | zero => simp_all
  | succ m' ih =>
    simp_all [genTy, bind, optBind_bind, pick, optPick_pick]
    match v with
    | .unit => simp_all
    | .arrow τ1 τ2 =>
      right
      match Or.symm (Nat.le_or_eq_of_le_succ hlt) with
      | .inl h =>
        subst h
        simp_all [genTy, bind, optBind_bind, pick, optPick_pick]
      | .inr h =>
        exists τ1
        apply And.intro
        . sorry
        . sorry

instance : Arbitrary Ty where
  arbitrary := ⟨
    Gen.sized genTy,
    by sorry
  ⟩

inductive Term : Type where
  | unit
  | var (n : Nat)
  | abs (τ : Ty) (t : Term)
  | app (t₁ t₂ : Term)

inductive TermF : Type → Type where
  | unitStep : TermF β
  | varStep : (n : Nat) → TermF β
  | absStep : (τ : Ty) → (t : β) → TermF β
  | appStep : (t₁ t₂ : β) → TermF β

def Term.fold (f : TermF β → β) : Term → β
  | .unit => f .unitStep
  | .var n => f (.varStep n)
  | .abs τ t => f (.absStep τ (Term.fold f t))
  | .app t₁ t₂ => f (.appStep (Term.fold f t₁) (Term.fold f t₂))

def Term.accu
    {β σ : Type}
    (stAbs : Ty → σ → σ)
    (stApp : σ → σ × σ)
    (f : TermF β → σ → β)
    (t : Term)
    (s : σ) :
    β :=
  match t with
  | .unit => f .unitStep s
  | .var n => f (.varStep n) s
  | .abs τ t => f (.absStep τ (Term.accu stAbs stApp f t (stAbs τ s))) s
  | .app t₁ t₂ =>
    let (s₁, s₂) := stApp s
    f (.appStep (Term.accu stAbs stApp f t₁ s₁) (Term.accu stAbs stApp f t₂ s₂)) s

def Term.accuM
    [Monad m]
    {β σ : Type}
    (stAbs : Ty → σ → σ)
    (stApp : σ → σ × σ)
    (f : TermF β → σ → m β)
    (t : Term)
    (s : σ) :
    m β :=
  match t with
  | .unit => f .unitStep s
  | .var n => f (.varStep n) s
  | .abs τ t => do f (.absStep τ (← Term.accuM stAbs stApp f t (stAbs τ s))) s
  | .app t₁ t₂ => do
    let (s₁, s₂) := stApp s
    f (.appStep (← Term.accuM stAbs stApp f t₁ s₁) (← Term.accuM stAbs stApp f t₂ s₂)) s

def Ctx := List Ty

def hasType_natural (Γ : Ctx) : Term → Option Ty
  | .unit => pure .unit
  | .var n => Γ.get? n
  | .abs τ t => .arrow τ <$> hasType_natural (τ :: Γ) t
  | .app t1 t2 => do
    match ← hasType_natural Γ t1 with
    | .arrow τ1 τ2 => do
      let τ3 ← hasType_natural Γ t2
      guard (τ1 == τ3)
      pure τ2
    | .unit => failure

def hasType_fold (Γ : Ctx) (t : Term) : Option Ty :=
  Term.fold
    (λ (s : TermF (Ctx → Option Ty)) =>
      match s with
      | .unitStep => λ _ => pure Ty.unit
      | .varStep n => λ Γ => Γ.get? n
      | .absStep τ hasType_t => λ Γ => .arrow τ <$> hasType_t (τ :: Γ)
      | .appStep hasType_t₁ hasType_t₂ => λ Γ => do
        match ← hasType_t₁ Γ with
        | .arrow τ1 τ2 => do
          let τ3 ← hasType_t₂ Γ
          guard (τ1 == τ3)
          pure τ2
        | .unit => failure)
    t
    Γ

def hasType_accu (Γ : Ctx) (t : Term) : Option Ty :=
  Term.accu
    (λ τ Γ => τ :: Γ)
    (λ Γ => (Γ, Γ))
    (λ (s : TermF (Option Ty)) Γ =>
      match s with
      | .unitStep => pure Ty.unit
      | .varStep n => Γ.get? n
      | .absStep τ τt => .arrow τ <$> τt
      | .appStep τt₁ τt₂ => do
        match ← τt₁ with
        | .arrow τ1 τ2 => do
          let τ3 ← τt₂
          guard (τ1 == τ3)
          pure τ2
        | .unit => failure)
    t
    Γ

def hasType_accuM (Γ : Ctx) (t : Term) : Option Ty :=
  Term.accuM
    (λ τ Γ => τ :: Γ)
    (λ Γ => (Γ, Γ))
    (λ (s : TermF Ty) Γ =>
      match s with
      | .unitStep => pure Ty.unit
      | .varStep n => Γ.get? n
      | .absStep τ τt => pure (.arrow τ τt)
      | .appStep τt₁ τt₂ =>
        match τt₁ with
        | .arrow τ1 τ2 => do guard (τ1 == τt₂); pure τ2
        | .unit => failure)
    t
    Γ
