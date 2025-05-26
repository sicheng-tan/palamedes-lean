import Palamedes.Support

/- Type definition -/
/- adapted from https://github.com/QuickChick/QuickChick/tree/master/examples/ifc-basic -/

inductive Label where
  | low
  | high

inductive Atom where
  | atm (z : Int) (l : Label)

inductive Stack where
  | mty
  | cons (a : Atom) (s : Stack)
  | ret_cons (pc : Atom) (s : Stack)

/- Base functor -/

inductive StackF (α : Type) where
  | mty : StackF α
  | cons : (z : Atom) → (s : α) → StackF α
  | ret_cons : (pc : Atom) → (s : α) → StackF α

theorem StackF_or
  {α : Type}
  {P : Prop}
  {Q : Atom → α → Prop}
  {R : Atom → α → Prop}
  {s : StackF α} :
  StackF.rec P Q R s ↔
    (P ∧ s = .mty)
    ∨ (∃ z s', s = .cons z s' ∧ Q z s')
    ∨ (∃ pc s', s = .ret_cons pc s' ∧ R pc s') := by
  match s with
  | .mty => simp
  | .cons _ _ => aesop
  | .ret_cons _ _ => aesop

/- Recursion schemes -/

def Stack.fold
  {α : Type}
  (f : (Atom ⊕ Atom) → α → α)
  (z : α)
  (s : Stack) : α :=
  match s with
  | .mty => z
  | .cons x s' => f (Sum.inl x) (Stack.fold f z s')
  | .ret_cons pc s' => f (Sum.inr pc) (Stack.fold f z s')

@[simp] theorem Stack.fold_mty : Stack.fold f z .mty = z := rfl
@[simp] theorem Stack.fold_cons {x} {s : Stack} {f : (Atom ⊕ Atom) → β → β} {z} :
    Stack.fold f z (.cons x s) = f (Sum.inl x) (Stack.fold f z s) := rfl
@[simp] theorem Stack.fold_ret_cons {x} {s : Stack} {f : (Atom ⊕ Atom) → β → β} {z} :
    Stack.fold f z (.ret_cons x s) = f (Sum.inr x) (Stack.fold f z s) := rfl

def Stack.accuM
  [Monad m]
  {α σ : Type}
  (st : (Atom ⊕ Atom) → σ → σ)
  (f : (Atom ⊕ Atom) → α → σ → m α)
  (z : σ → m α)
  (s : Stack)
  (i : σ) : m α :=
  match s with
  | .mty => z i
  | .cons x s' => do
     f (Sum.inl x) (← Stack.accuM st f z s' (st (Sum.inl x) i)) i
  | .ret_cons pc s' => do
     f (Sum.inr pc) (← Stack.accuM st f z s' (st (Sum.inr pc) i)) i

/- (unclear if we need these) -/
@[simp] theorem Stack.accuM_nil [Monad m] {st : (Atom ⊕ Atom) → σ → σ}
  {f : (Atom ⊕ Atom) → β → σ → m β} {z : σ → m β} {i : σ} :
  Stack.accuM st f z .mty i = z i := rfl
@[simp] theorem Stack.accuM_cons  [Monad m] {st : (Atom ⊕ Atom) → σ → σ}
  {f : (Atom ⊕ Atom) → β → σ → m β} {z : σ → m β} {i : σ} {z} {x} {s : Stack} :
    Stack.accuM st f z (.cons x s) i
    = (do f (Sum.inl x) (← Stack.accuM st f z s (st (Sum.inl x) i)) i) := rfl
@[simp] theorem Stack.accuM_ret_cons [Monad m] {st : (Atom ⊕ Atom) → σ → σ}
  {f : (Atom ⊕ Atom) → β → σ → m β} {z : σ → m β} {i : σ} {z} {pc} {s : Stack} :
    Stack.accuM st f z (.ret_cons pc s) i
    = (do f (Sum.inr pc) (← Stack.accuM st f z s (st (Sum.inr pc) i)) i) := rfl

-- theorem Stack.accuM_mty
-- theorem Stack.accuM_cons
-- theorem Stack.accuM_ret_cons

/- Fold special cases -/

theorem Stack.fold_accu_Option_basic
    {α : Type}
    {v : α}
    {s : Stack}
    {z : α}
    {f : (Atom ⊕ Atom) → α → α} :
    Stack.fold f z s = v ↔
    Stack.accuM
      (fun _ _ => ())
      (fun x s' _ => some (f x s'))
      (fun _ => some z)
      s
      () = some v := by
    induction s generalizing v <;> simp_all [Stack.fold, Stack.accuM]
    case cons x s' ih =>
      replace ih := @ih (Stack.fold f z s')
      simp_all [Stack.fold, Stack.accuM]
    case ret_cons pc s' ih =>
      replace ih := @ih (Stack.fold f z s')
      simp_all [Stack.fold, Stack.accuM]

theorem Stack.fold_accu_Option_true
    {s : Stack}
    {g : (Atom ⊕ Atom) → Bool}
    {f : (Atom ⊕ Atom) → Bool → Bool}
    (h : ∀ x acc, f x acc = (g x && acc)) :
    Stack.fold f true xs = true ↔
    Stack.accuM
      (fun _ _ => ())
      (fun x _ _ => guard (g x))
      (fun _ => some ())
      xs
      () = some () := by
    induction xs <;> simp_all [Stack.fold, Stack.accuM]
    case cons x s' ih =>
        apply Iff.intro <;> intro hf
        . -- (->)
          generalize hv : fold f true s' = v
          cases v <;>
            simp_all [Stack.fold, Stack.accuM, guard]
        . -- (<-)
          rw [Option.bind_eq_some] at hf
          replace ⟨ v, hf ⟩ := hf
          simp_all [Stack.fold, Stack.accuM, guard]
    case ret_cons pc s' ih =>
        apply Iff.intro <;> intro hf
        . -- (->)
          generalize hv : fold f true s' = v
          cases v <;>
            simp_all [Stack.fold, Stack.accuM, guard]
        . -- (<-)
          rw [Option.bind_eq_some] at hf
          replace ⟨ v, hf ⟩ := hf
          simp_all [Stack.fold, Stack.accuM, guard]


-- theorem Stack.fold_accu_Option_basic
-- theorem Stack.fold_accu_Option_true
-- theorem Stack.fold_accu_Option_function
-- theorem Stack.fold_accu_Option_function_true

/- Unfold -/

def Stack.unfold (n : Nat) (f : α → Gen (StackF α)) (x : α)
  : Gen (Option Stack) :=
  match n with
  | 0 => pure none
  | n' + 1 => do
    match (← f x) with
    | .mty => pure (some .mty)
    | .cons x vs => do
      let s ← Stack.unfold n' f vs
      pure (do pure (.cons x (← s)))
    | .ret_cons pc vs => do
      let s ← Stack.unfold n' f vs
      pure (do pure (.ret_cons pc (← s)))
-- def Stack.unfold_support
-- theorem Stack.unfold_monotonic
-- theorem Stack.unfold_support_ok

/- Conversion of recursive functions to fold -/
-- theorem Stack.coerce_to_fold

/- Merging two accumulators-/
-- theorem Stack.merge_accuM


/- Pretty printing -/
def Label.toString : Label → String
  | .low => "low"
  | .high => "high"

instance : ToString Label where
  toString := Label.toString

def Atom.toString : Atom → String
  | .atm z l => s!"({z} {l})"

instance : ToString Atom where
  toString := Atom.toString

def Stack.toString : Stack → String
  | .mty => "(empty)"
  | .cons a s  => s!"(cons {a} {Stack.toString s})"
  | .ret_cons pc s => s!"(ret_cons {pc} {Stack.toString s})"

instance : ToString Stack where
  toString := Stack.toString

/- Arbitrary instances for supporting types -/

instance : Arbitrary Label where
  arbitrary := ⟨
      pick (pure .low) (pure .high),
      by intro v <;> cases v <;> simp [pick, optPick]
    ⟩

instance : Arbitrary Int where
  arbitrary := ⟨
      bind Arbitrary.arbitrary.val (λ n => pick (pure (Int.ofNat n)) (pure (Int.negSucc n))),
      by
        intro v
        simp [-support, bind, optBind_bind]
        cases v
        case ofNat n =>
          exists n
          rw [Arbitrary.arbitrary.property] <;> simp [pick, optPick_pick]
        case negSucc n =>
          exists n
          rw [Arbitrary.arbitrary.property] <;> simp [pick, optPick_pick]
    ⟩

instance : Arbitrary Atom where
  arbitrary := ⟨
      bind Arbitrary.arbitrary.val (λ z => bind Arbitrary.arbitrary.val (λ l => pure $ .atm z l)),
      by
        simp [bind, optBind_bind, Arbitrary.arbitrary.property]
        intro ⟨ z, l ⟩
        exists z, l
    ⟩
