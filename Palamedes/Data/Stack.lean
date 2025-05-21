import Palamedes.Support

/- Type definition -/
/- adapted from https://github.com/QuickChick/QuickChick/tree/master/examples/ifc-basic -/

inductive Label where
  | L
  | H

inductive Atom where
  | atm (z : Int) (l : Label)

inductive Stack where
  | mty
  | cons (a : Atom) (s : Stack)
  | ret_cons (pc : Atom) (s : Stack)

/- Arbitrary instances -/

instance : Arbitrary Label where
  arbitrary := ⟨
      pick (pure .L) (pure .H),
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

/- base functor for Stack -/

inductive StackF (α : Type) where
  | mty : StackF α
  | cons : (z : Atom) → (s : α) → StackF α
  | ret_cons : (pc : Atom) → (s : α) → StackF α

#print StackF.rec

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

/- Folds, etc. -/

-- fold variants
-- def Stack.fold
-- def Stack.foldM
-- def Stack.accu
-- def Stack.accuM

-- theorem fold_mty
-- theorem fold_cons
-- theorem fold_ret_cons

-- theorem foldM_mty
-- theorem foldM_cons
-- theorem foldM_ret_cons

-- theorem accu_mty
-- theorem accu_cons
-- theorem accu_ret_cons

-- theorem accuM_mty
-- theorem accuM_cons
-- theorem accuM_ret_cons

-- relationships between fold variants

-- theorem fold_foldM
-- theorem fold_accu
-- theorem fold_accuM

-- unfold

-- def unfoldStack
-- def unfoldStack_support
-- def support_unfoldStack
-- theorem unfoldStack_monotonic
-- theorem support_unfoldStack
-- theorem support_unfoldStack_ok

-- merge lemmas

-- theorem merge_fold
-- theorem merge_foldM
-- theorem merge_accu
-- theorem merge_accuM

-- coercion lemmas

-- theorem coerce_to_fold
-- theorem coerce_to_foldM
-- theorem coerce_to_accu
-- theorem coerce_to_accuM

/- Pretty printing -/
def labelToString : Label → String
  | .L => "L"
  | .H => "H"

instance : ToString Label where
  toString := labelToString

def atomToString : Atom → String
  | .atm z l => s!"({z} {l})"

instance : ToString Atom where
  toString := atomToString

def stackToString : Stack → String
  | .mty => "(empty)"
  | .cons a s  => s!"(cons {a} {stackToString s})"
  | .ret_cons pc s => s!"(ret_cons {pc} {stackToString s})"

instance : ToString Stack where
  toString := stackToString
