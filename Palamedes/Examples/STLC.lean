import Palamedes.Synth

inductive Ty : Type where
  | unit
  | arrow (τ₁ τ₂ : Ty)
  deriving DecidableEq

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

def Term.unfold' (n : Nat) (f : β → Gen (TermF β)) (b : β) : Gen (Option Term) :=
  match n with
  | 0 => pure none
  | n + 1 => do
    match (← f b) with
    | .unitStep => pure (some .unit)
    | .varStep n => pure (some (.var n))
    | .absStep τ bt => do
      let t ← Term.unfold' n f bt
      pure (do pure (.abs τ (← t)))
    | .appStep bt₁ bt₂ => do
      let t₁ ← Term.unfold' n f bt₁
      let t₂ ← Term.unfold' n f bt₂
      pure (do pure (.app (← t₁) (← t₂)))

def Term.unfold (f : β → Gen (TermF β)) (b : β) : Gen Term :=
  Gen.sized (λ n => Term.unfold' n f b)

@[simp]
def Term.unfold_support (P : β → TermF β → Prop) (b : β) : Term → Prop
  | .unit => P b .unitStep
  | .var n => P b (.varStep n)
  | .abs τ t => ∃ bt, P b (.absStep τ bt) ∧ Term.unfold_support P bt t
  | .app t₁ t₂ => ∃ bt₁ bt₂,
    P b (.appStep bt₁ bt₂) ∧
    Term.unfold_support P bt₁ t₁ ∧
    Term.unfold_support P bt₂ t₂

theorem Term.unfold_unfold_support :
    support (Term.unfold f b) = Term.unfold_support (λ b' => support (f b')) b := by
  sorry

abbrev Term.synth_accuM
    {β σ : Type}
    {stAbs : Ty → σ → σ}
    {stApp : σ → σ × σ}
    {f : TermF β → σ → Option β}
    {s : σ}
    {b : β}
    (g : (b : β) → (s : σ) → CGen
      (TermF.rec
        (f .unitStep s = some b)
        (λ n => f (.varStep n) s = some b)
        (λ τ t => f (.absStep τ t) s = some b)
        (λ t₁ t₂ => f (.appStep t₁ t₂) s = some b))) :
    CGen (λ (v : Term) => Term.accuM stAbs stApp f v s = some b) := by
  exists Term.unfold
    (λ (b, s) => do
      match (← (g b s).val) with
      | .unitStep => pure .unitStep
      | .varStep n => pure (.varStep n)
      | .absStep τ bt => do
        let s' := stAbs τ s
        pure (.absStep τ (bt, s'))
      | .appStep bt₁ bt₂ => do
        let (s₁, s₂) := stApp s
        pure (.appStep (bt₁, s₁) (bt₂, s₂)))
    (b, s)
  intro v
  rw [Term.unfold_unfold_support]
  induction v generalizing b s with
  | unit =>
    simp_all [Term.accuM, bind, optBind_bind]
    have g_prop := (g b s).property .unitStep
    aesop
  | var n =>
    simp_all [Term.accuM, bind, optBind_bind]
    have g_prop := (g b s).property (.varStep n)
    aesop
  | abs τ t ih =>
    simp_all [Term.accuM, bind, optBind_bind]
    generalize ho : accuM stAbs stApp f t (stAbs τ s) = o at *
    match o with
    | none => aesop
    | some bt =>
      have g_prop := (g b s).property (.absStep τ bt)
      aesop
  | app t₁ t₂ ih₁ ih₂ =>
    simp_all [Term.accuM, bind, optBind_bind]
    generalize ho₁ : accuM stAbs stApp f t₁ (stApp s).fst = o₁ at *
    match o₁ with
    | none => aesop
    | some bt₁ =>
      generalize ho₂ : accuM stAbs stApp f t₂ (stApp s).snd = o₂ at *
      match o₂ with
      | none => aesop
      | some bt₂ =>
        have g_prop := (g b s).property (.appStep bt₁ bt₂)
        simp_all [Option.some_bind]
        rw [← g_prop]
        apply Iff.intro
        . aesop
        . intro h
          exists bt₁
          exists (stApp s).fst
          exists bt₂
          exists (stApp s).snd
          aesop

theorem Ty.deforest_eq
    {b b_unit : β}
    {b_arrow : Ty → Ty → β} :
    Ty.rec b_unit (λ τ₁ τ₂ _ _ => b_arrow τ₁ τ₂) τ = b ↔
    Ty.rec (b_unit = b) (λ τ₁ τ₂ _ _ => b_arrow τ₁ τ₂ = b) τ := by
  induction τ <;> aesop

theorem Ty.as_or
    {P_unit : Prop}
    {P_arrow : Ty → Ty → Prop} :
    Ty.rec P_unit (λ τ₁ τ₂ _ _ => P_arrow τ₁ τ₂) τ ↔
    (τ = .unit ∧ P_unit) ∨ (∃ τ₁ τ₂, τ = .arrow τ₁ τ₂ ∧ P_arrow τ₁ τ₂) := by
  induction τ <;> aesop

theorem TermF.as_or :
    TermF.rec P_unit P_var P_app P_abs t ↔
    ((t = .unitStep ∧ P_unit) ∨
     (∃ n, t = .varStep n ∧ P_var n) ∨
     (∃ τ t', t = .absStep τ t' ∧ P_app τ t') ∨
     (∃ t₁ t₂, t = .appStep t₁ t₂ ∧ P_abs t₁ t₂)) := by
  induction t <;> aesop

def Gen.elements (xs : List α) (h : xs.length > 0 := by simp_all) : Gen α :=
  match xs with
  | x :: xs =>
    match hxs : xs with
    | [] => pure x
    | _ :: _ => pick (pure x) (Gen.elements xs)

theorem Gen.elements_support
    {xs : List α} {v : α} {h : xs.length > 0} :
    v ∈ 〚Gen.elements xs h〛↔ v ∈ xs := by
  induction xs with
  | nil => simp_all; contradiction
  | cons x xs ih =>
    match hxs : xs with
    | [] => simp_all
    | _ :: _ => simp_all

def Gen.indicesOf [DecidableEq α] (xs : List α) (a : α) : Gen Nat :=
  let inds := (xs.enum.filter (λ (_, x) => x == a)).map (λ (n, _) => n)
  .guardIn (inds.length > 0)
           (if h : inds.length > 0 then isTrue h else isFalse h)
           (λ h => Gen.elements inds h)

def synth_get? [DecidableEq α] {xs : List α} {a : α} : CGen (fun (n : Nat) => xs[n]? = some a) := by
  exists Gen.indicesOf xs a
  intro v
  simp [Gen.indicesOf, Gen.elements_support]
  apply Iff.intro
  . intro ⟨_, h2⟩
    exact List.mk_mem_enum_iff_getElem?.mp h2
  . intro h
    apply And.intro
    . rw [← List.mk_mem_enum_iff_getElem?] at h
      apply List.length_pos_of_mem
      simp_all only [List.mem_filter, beq_iff_eq]
      apply And.intro
      · exact h
      · simp_all only
    . exact List.mk_mem_enum_iff_getElem?.mpr h

theorem Option.rec_exists : Option.rec False (λ _ => True) o ↔ ∃ v, o = some v := by
  match o with
  | none => simp
  | some v => simp

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

@[simp]
def hasType (Γ : Ctx) (t : Term) : Option Ty :=
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

def genWellTyped_manual (Γ : Ctx) : CGen (λ (v : Term) =>
    match hasType Γ v with
    | some _ => True
    | none => False) := by
  unfold genWellTyped_manual.match_1
  simp [Option.rec_exists]
  apply synth_bind_arb
  intro τ
  apply Term.synth_accuM
  intro τ Γ
  simp [TermF.as_or]
  match τ with
  | .unit =>
    simp
    apply synth_or
    . apply synth_pure
    . apply synth_or
      . conv => congr; intro v; congr; intro x; rw [and_comm]
        apply synth_bind
        . apply synth_get?
        . intro n
          apply synth_pure
      . unfold hasType_natural.match_1
        simp_all [guard, ite, failure, deforest_decidable_bind, deforest_decidable_eq, decidable_or, Ty.deforest_eq, Ty.as_or]
        conv => congr; intro v; rw [exists_comm]
        apply synth_bind_arb
        intro τ₁
        conv => congr; intro v; congr; intro x; rw [and_comm]
        apply synth_bind
        . apply synth_pure
        . intro τ₂
          apply synth_pure
  | .arrow τ₁ τ₂ =>
    simp
    apply synth_or
    . conv => congr; intro v; congr; intro x; rw [and_comm]
      apply synth_bind
      . apply synth_get?
      . intro n
        apply synth_pure
    . apply synth_or
      . apply synth_pure
      . unfold hasType_natural.match_1
        set_option smartUnfolding false in
        simp_all [guard, ite, failure, deforest_decidable_bind, deforest_decidable_eq, decidable_or, Ty.deforest_eq, Ty.as_or]
        conv => congr; intro v; rw [exists_comm]
        apply synth_bind_arb
        intro τ₁
        conv => congr; intro v; congr; intro x; rw [and_comm]
        apply synth_bind
        . apply synth_pure
        . intro τ₂
          apply synth_pure

attribute [simp]
  guard
  failure
  ite
  deforest_decidable_bind
  deforest_decidable_eq
  decidable_or
  Ty.deforest_eq
  Ty.as_or
  TermF.as_or
  ListF_or
  TreeF_or
  fold_foldM
  merge_foldM
  Option.rec_exists
attribute [-simp]
  Prod.forall
attribute [-aesop]
  Subtype
add_aesop_rules unsafe [
  apply synth_bind,
  apply synth_bind_arb,
  apply synth_or,
  apply synth_pure,
  apply synth_true,
  apply synth_tuple,
  apply synth_unfoldM,
  apply synth_accuM,
  apply synth_accuTreeM,
  apply synth_between,
  apply Term.synth_accuM,
  (by apply Term.synth_accuM; intro b s; cases b),
  apply synth_get?,
  (by (conv => congr; intro v; congr; intro x; rw [and_comm]); apply synth_bind),
  (by (conv => congr; intro v; rw [eq_comm]); apply synth_pure),
  (by (conv => congr; intro v; rw [exists_comm]); apply synth_bind_arb),
]

def genWellTyped (Γ : Ctx) : CGen (λ (v : Term) =>
    match hasType Γ v with
    | some _ => True
    | none => False) := by
  aesop
    (add unsafe (by unfold hasType_natural.match_1))
    (add unsafe (by unfold genWellTyped_manual.match_1))
