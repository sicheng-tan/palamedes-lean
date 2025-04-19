import Palamedes.Support
import Palamedes.Data.List
import Palamedes.Data.Tree
import Palamedes.Decidable
import Palamedes.RuleSets
import Palamedes.InternalizeProofs

abbrev synth_pure
    (v' : α) :
    CGen (λ v => v = v') :=
  Subtype.mk (pure v') <| by
    simp

abbrev synth_bind
    {P : α → Prop}
    {Q : α → β → Prop}
    [(x : α) → Decidable (P x)]
    (hb : CGen P)
    (hf : (a : {v : α // P v}) → CGen (Q a)) :
    CGen (λ v => ∃ a, P a ∧ Q a v) :=
  Subtype.mk (optBind (hb.internalizeProofs).val λ a => (hf a).val) <| by
    intro v
    rw [optBind_bind]
    obtain ⟨val, property⟩ := hb
    apply Iff.intro
    . rintro ⟨a, ha⟩
      exists a
      have := (hf a).property
      simp_all only [support, exists_const, true_and, and_self]
      simp
      exact a.property
    . rintro ⟨a, ha⟩
      simp_all only [support, exists_const, true_and, and_self, CGen.internalizeProofs, bind, optBind_bind]
      simp
      exists a
      apply And.intro
      . have := (property a).mpr ha.left
        exists this
        exact injProof_correct this
      . exists ha.left
        apply ((hf ⟨a, ha.left⟩).property v).mpr
        exact ha.right

abbrev synth_bind_arb
    [Arbitrary α]
    {Q : α → β → Prop}
    (g : (a : α) → CGen (Q a)) :
    CGen (λ v => ∃ a, Q a v) :=
  let ⟨arb_val, arb_property⟩ := @Arbitrary.arbitrary α _
  Subtype.mk (do let x ← arb_val; (g x).val) <| by
    intro b
    simp_all
    apply Iff.intro
    · simp [bind, optBind_bind]
      rintro v'
      have := (g v').property
      simp_all
      intro hv
      exists v'
    · rintro ⟨v', hv'⟩
      have := (g v').property
      simp [bind, optBind_bind]
      exists v'
      simp_all

abbrev synth_tuple
    {P : α → Prop}
    {Q : α → β → Prop}
    {R : α × β → Prop}
    {h : ∀ v, P v.1 ∧ Q v.1 v.2 ↔ R v}
    (gx : CGen P)
    (gy : (x : α) → CGen (Q x)) :
    CGen R :=
  let ⟨gx_val, gx_prop⟩ := gx
  Subtype.mk
    (do
      let x ← gx_val
      let y ← (gy x).val
      pure (x, y))
    (by
      simp_all [-Prod.forall, bind, optBind_bind]
      intro ⟨x, y⟩
      have gy_prop := (gy x).property
      simp_all)

abbrev synth_or
    {P Q : α → Prop}
    (x : CGen P)
    (y : CGen Q) :
    CGen (λ v => P v ∨ Q v) :=
  Subtype.mk (pick x.val y.val) <| by
    simp [pick, optPick_pick]
    aesop

abbrev synth_unfoldM
    {α β : Type}
    {f : α → β → Option β}
    {b z : β}
    (g : (b : β) → CGen (ListF.rec (b = z) (λ a b' => f a b' = some b))) :
    CGen (λ v => List.foldrM f z v = .some b) :=
  Subtype.mk (.sized (λ n => unfoldr' n (λ b => (g b).val) b)) <| by
    rw [support_unfoldr']
    intro v
    induction v generalizing b with
    | nil =>
      have := (g b).property .nil
      simp_all [Eq.comm]
    | cons x xs ih =>
      have := (g b).property
      simp_all
      match List.foldrM f z xs with
      | .none => simp_all
      | .some b' => aesop

abbrev synth_accu
    {α β σ : Type}
    {st : α → σ → σ}
    {f : α → β → σ → β}
    {z : σ → β}
    {s : σ}
    {b : β}
    (g : (b : β) → (s : σ) → CGen (ListF.rec (z s = b) (λ a b' => f a b' s = b))) :
    CGen (λ v => List.accu st f z v s = b) :=
  Subtype.mk
    (.sized (λ n => unfoldr' n (λ (b, s) => do
      match (← (g b s).val) with
      | .nil => pure .nil
      | .cons x b' => pure (.cons x (b', st x s))) (b, s)))
    (by
      rw [support_unfoldr']
      simp_all
      intro v
      rw [←foldr_accu]
      on_goal 2 => exact Eq.refl _
      induction v generalizing s b with
      | nil =>
        have := (g b s).property .nil
        simp_all [bind, optBind_bind]
        aesop
      | cons x xs ih =>
        have := (g b s).property (.cons x (List.foldr (fun x b s => f x (b (st x s)) s) z xs (st x s)))
        simp_all [bind, optBind_bind]
        aesop)

abbrev synth_accuM
    {α β σ : Type}
    {st : α → σ → σ}
    {f : α → β → σ → Option β}
    {z : σ → Option β}
    {s : σ}
    {b : β}
    (g : (b : β) → (s : σ) → CGen (ListF.rec (z s = some b) (λ a b' => f a b' s = some b))) :
    CGen (λ v => List.accuM st f z v s = some b) :=
  Subtype.mk
    (.sized (λ n => unfoldr' n (λ (b, s) => do
      match (← (g b s).val) with
      | .nil => pure .nil
      | .cons x b' => pure (.cons x (b', st x s))) (b, s)))
    (by
      rw [support_unfoldr']
      simp_all
      intro xs
      rw [←foldr_accuM]
      on_goal 2 => exact Eq.refl _
      induction xs generalizing s b with
      | nil =>
        have := (g b s).property .nil
        simp_all [bind, optBind_bind]
        aesop
      | cons x xs ih =>
        simp_all
        clear ih
        aesop (config := {warnOnNonterminal := false})
        . have := (g b s).property
          simp_all [bind, optBind_bind]
          aesop
        . have := (g b s).property
          simp_all
          generalize ho : List.foldr (fun x b s => do f x (← b (st x s)) s) z xs (st x s) = o at *
          match o with
          | .none => simp_all
          | .some b' =>
            simp_all
            exists b'
            exists st x s
            apply And.intro
            . simp_all [bind, optBind_bind]
              exists .cons x b'
            . rw [ho])

abbrev synth_accuTreeM
    {α β σ : Type}
    {st : α → σ → σ × σ}
    {f : β → α → β → σ → Option β}
    {z : σ → Option β}
    {s : σ}
    {b : β}
    (g : (b : β) → (s : σ) → CGen (TreeF.rec (z s = some b) (λ bl a br => f bl a br s = some b))) :
    CGen (λ v => Tree.accuM st f z v s = some b) :=
  Subtype.mk
    (.sized (λ n => unfoldTree n (λ (b, s) => do
      match (← (g b s).val) with
      | .leaf => pure .leaf
      | .node bl x br =>
        let (sl, sr) := st x s
        pure (.node (bl, sl) x (br, sr))) (b, s)))
  (by
    rw [support_unfoldTree_ok]
    simp_all
    intro t
    induction t generalizing s b with
    | leaf =>
      have := (g b s).property .leaf
      simp_all [bind, optBind_bind]
      aesop (add simp Tree.accuM)
    | node l x r ih =>
      simp_all
      clear ih
      aesop
        (config := {warnOnNonterminal := false})
        (add simp Tree.accuM)
      . have := (g b s).property
        simp_all [bind, optBind_bind]
        aesop
      . have := (g b s).property
        simp_all
        generalize hol : Tree.accuM st f z l (st x s).fst = o_l at *
        match o_l with
        | .none => simp_all
        | .some bl =>
          simp_all
          generalize hor : Tree.accuM st f z r (st x s).snd = o_r at *
          match o_r with
          | .none => simp_all
          | .some br =>
            exists bl
            exists (st x s).fst
            exists br
            exists (st x s).snd
            simp_all [bind, optBind_bind]
            exists (.node bl x br))

abbrev synth_true
    [Arbitrary α] :
    CGen (λ (_ : α) => True) :=
  @Arbitrary.arbitrary α _

abbrev synth_between
    {lo hi : Nat} :
    CGen (λ v => lo ≤ v ∧ v ≤ hi) :=
  Subtype.mk (.guardIn (lo ≤ hi) (Nat.decLe lo hi) (choose lo hi ·)) <| by
    intro v
    simp_all
    exact Nat.le_trans

abbrev synth_gt
  {lo : Nat} :
  CGen (λ v => lo < v) := Subtype.mk (gt lo) (by apply gt_support)

abbrev synth_conv
    (h : P = Q)
    (g : CGen P) :
    CGen Q :=
  Subtype.mk g.val <| by
    intro v
    rw [←h]
    exact g.property v

macro "#set_up_palamedes_simp" : command =>
  `(attribute [local simp]
      guard
      failure
      ite -- NOTE This may be a problem
      deforest_decidable_bind
      deforest_decidable_eq
      decidable_or
      ListF_or
      TreeF_or
      fold_foldM
      merge_foldM

    attribute [-simp] Prod.forall)

-- attribute [simp]
--   guard
--   failure
--   ite -- NOTE This may be a problem
--   deforest_decidable_bind
--   deforest_decidable_eq
--   decidable_or
--   ListF_or
--   TreeF_or
--   fold_foldM
--   merge_foldM

-- attribute [-simp] Prod.forall

add_aesop_rules unsafe (rule_sets := [palamedes]) [
  apply synth_bind,
  apply synth_bind_arb,
  apply synth_or,
  apply synth_pure,
  apply synth_gt,
  apply synth_true,
  apply synth_tuple,
  apply synth_unfoldM,
  apply synth_accuM,
  apply synth_accuTreeM,
  apply synth_between,
  (by apply synth_conv (by ext v; conv => rhs; congr; intro a; rw [and_comm]) (synth_bind _ _)),
  (by apply synth_conv (by aesop (config := {maxRuleApplications := 10, maxRuleApplicationDepth := 10, terminal := true})) (synth_pure _)),
]

add_aesop_rules 5% (rule_sets := [palamedes]) [
  cases Nat,
  cases Bool,
]

macro "simp_in_proof" : tactic =>
  `(tactic|apply synth_conv (by conv => simp) _)

macro "palamedes" : tactic =>
  `(tactic|aesop
    (config := {maxRuleApplicationDepth := 0, maxRuleApplications := 0})
    (rule_sets := [palamedes])
    (erase Subtype))

macro "palamedes?" : tactic =>
  `(tactic|aesop?
    (config := {maxRuleApplicationDepth := 0, maxRuleApplications := 0})
    (rule_sets := [palamedes])
    (erase Subtype))
