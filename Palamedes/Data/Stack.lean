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



/- (unclear if we need these) -/
-- theorem Stack.accuM_mty
-- theorem Stack.accuM_cons
-- theorem Stack.accuM_ret_cons

/- Fold special cases -/

-- theorem Stack.fold_accu_Option_basic
-- theorem Stack.fold_accu_Option_true
-- theorem Stack.fold_accu_Option_function
-- theorem Stack.fold_accu_Option_function_true

/- Unfold -/

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
