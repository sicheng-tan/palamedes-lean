import Palamedes.Free
import Palamedes.Support
import Palamedes.Util
import Palamedes.List
import Palamedes.Tree

theorem foldr_accu
    {α β σ : Type}
    {st : α → σ → σ}
    {s : σ}
    {xs : List α}
    {z : σ → β}
    {f : α → β → σ → β}
    {f' : α → (σ → β) → σ → β} :
    f' = (λ x b => λ s => f x (b (st x s)) s) →
    List.foldr f' z xs s = List.accu st f z xs s := by
  induction xs generalizing s <;> simp_all [List.accu]

theorem foldr_accuM
    [Monad m]
    {α β σ : Type}
    {st : α → σ → σ}
    {s : σ}
    {xs : List α}
    {z : σ → m β}
    {f : α → β → σ → m β}
    {f' : α → (σ → m β) → σ → m β} :
    f' = (λ x b => λ s => do f x (← b (st x s)) s) →
    List.foldr f' z xs s = List.accuM st f z xs s := by
  induction xs generalizing s <;> simp_all [List.accuM]

theorem deforest_decidable_bind
    {α β : Type}
    {p : Prop}
    {b : Decidable p}
    {f : α → Option β}
    {x : ¬p → Option α}
    {y : p → Option α} :
    (Decidable.rec x y b : Option α).bind f =
      (Decidable.rec (λ h => (x h).bind f) (λ h => ((y h).bind f)) b : Option β) := by
  match b with
  | isFalse h => simp
  | isTrue h => simp

theorem deforest_decidable_eq
    {α : Type}
    {p : Prop}
    {b : Decidable p}
    {a : α}
    {x : ¬p → α}
    {y : p → α} :
    (Decidable.rec x y b : α) = a ↔
      (Decidable.rec (λ h => x h = a) (λ h => y h = a) b : Prop) := by
  match b with
  | isFalse h => simp
  | isTrue h => simp

theorem decidable_or
    {P : Prop}
    {Q : Prop}
    {R : Prop}
    {b : Decidable P} :
    (Decidable.rec (λ _ => Q) (λ _ => R) b : Prop) ↔ ¬P ∧ Q ∨ P ∧ R := by
  match b with
  | isFalse h => simp_all
  | isTrue h => simp_all

theorem ListF_or
    {α β : Type}
    {P : Prop}
    {Q : α → β → Prop}
    {t : ListF α β} :
    ListF.rec P Q t ↔ (P ∧ t = .nil) ∨ (∃ x b, t = .cons x b ∧ Q x b) := by
  match t with
  | .nil => simp
  | .cons x b => aesop

theorem TreeF_or
    {α β : Type}
    {P : Prop}
    {Q : β → α → β → Prop}
    {t : TreeF α β} :
    TreeF.rec P Q t ↔ (P ∧ t = .leaf) ∨ (∃ bl x br, t = .node bl x br ∧ Q bl x br) := by
  match t with
  | .leaf => simp
  | .node _ _ _ => aesop

theorem fold_foldM
    {α β : Type}
    {f : α → β → β}
    {z b : β}
    {xs : List α} :
    List.foldr f z xs = b ↔ List.foldrM (λ x b => Option.some (f x b)) z xs = Option.some b := by
  induction xs generalizing b with
  | nil => simp_all
  | cons x xs ih =>
    simp_all only [List.foldr_cons, List.foldrM_cons, Option.bind_eq_bind]
    apply Iff.intro
    · intro a
      subst a
      generalize List.foldrM (fun x b => some (f x b)) z xs = o at *
      match o with
      | .none => simp_all
      | .some v =>
        simp_all
        rw [ih.mp]
        simp
    · intro a
      generalize List.foldrM (fun x b => some (f x b)) z xs = o at *
      match o with
      | .none => simp_all
      | .some v =>
        simp_all
        rw [(@ih v).mpr]
        simp_all
        rfl

theorem merge_foldM
    {α β₁ β₂: Type}
    {f₁ : α → β₁ → Option β₁}
    {f₂ : α → β₂ → Option β₂}
    {z₁ b₁ : β₁}
    {z₂ b₂ : β₂}
    {xs : List α} :
    (List.foldrM f₁ z₁ xs = some b₁ ∧ List.foldrM f₂ z₂ xs = some b₂) ↔
    List.foldrM (λ x b => do (← f₁ x b.fst, ← f₂ x b.snd)) (z₁, z₂) xs = some (b₁, b₂) := by
  induction xs generalizing b₁ b₂ with
  | nil => simp_all
  | cons x xs ih =>
    simp_all
    apply Iff.intro
    . intro h
      generalize List.foldrM f₁ z₁ xs = mx₁ at *
      generalize List.foldrM f₂ z₂ xs = mx₂ at *
      match mx₁, mx₂ with
      | .none, _ => simp_all
      | _, .none => simp_all
      | .some x₁, .some x₂ =>
        rw [(@ih x₁ x₂).mp (by simp_all)]
        simp_all
    . intro h
      generalize List.foldrM
        (fun x b =>
          (f₁ x b.fst).bind fun __do_lift => (f₂ x b.snd).bind fun __do_lift_1 => some (__do_lift, __do_lift_1))
        (z₁, z₂) xs = o at *
      match o with
      | .none => simp_all
      | .some (b₁, b₂) =>
        simp_all
        have ⟨h₁, h₂⟩ := (@ih b₁ b₂).mpr (by simp_all)
        rw [h₁]
        rw [h₂]
        simp_all
        generalize f₁ x b₁ = o₁ at *
        generalize f₂ x b₂ = o₂ at *
        match o₁, o₂ with
        | .none, _ => simp_all
        | _, .none => simp_all
        | .some x₁, .some x₂ => simp_all

abbrev synth_pure
  (v' : α) :
  CGen (λ v => v = v') := by
  exists (pure v')
  simp

abbrev synth_pure'
  (v' : α) :
  CGen (λ v => v' = v) := by
  exists (pure v')
  simp_all [Eq.comm]

abbrev synth_bind
    {P : α → Prop}
    {Q : α → β → Prop}
    (hb : CGen P)
    (hf : (a : α) → CGen (Q a)) :
    CGen (λ v => ∃ a, P a ∧ Q a v) := by
  exists .bind hb.val λ a => (hf a).val
  intro v
  obtain ⟨val, property⟩ := hb
  apply Iff.intro <;>
    (rintro ⟨a, ha⟩; exists a; have := (hf a).property; simp_all only [and_self])

abbrev synth_bind_arb
    [Arbitrary α]
    {Q : α → β → Prop}
    (g : (a : α) → CGen (Q a)) :
    CGen (λ v => ∃ a, Q a v) := by
  obtain ⟨arb_val, arb_property⟩ := @Arbitrary.arbitrary α _
  exists (do let x ← arb_val; (g x).val)
  intro b
  simp_all
  apply Iff.intro
  · rintro ⟨v', hv'⟩
    have := (g v').property
    simp_all
    exists v'
  · rintro ⟨v', hv'⟩
    have := (g v').property
    exists v'
    simp_all

abbrev synth_tuple
    {P : α → Prop}
    {Q : α → β → Prop}
    {R : α × β → Prop}
    {h : ∀ p, P p.fst ∧ Q p.fst p.snd ↔ R p}
    (gx : CGen P)
    (gy : (x : α) → CGen (Q x)) :
    CGen R := by
  have ⟨gx_val, gx_prop⟩ := gx
  exists (do
    let x ← gx_val
    let y ← (gy x).val
    pure (x, y))
  simp_all [-Prod.forall]
  intro ⟨x, y⟩
  have gy_prop := (gy x).property
  simp_all

abbrev synth_or
    {P Q : α → Prop}
    (x : CGen P)
    (y : CGen Q) :
    CGen (λ v => P v ∨ Q v) := by
  have ⟨gx, hx⟩ := x
  have ⟨gy, hy⟩ := y
  exists (do
    let b ← choose 0 1
    if b == 0 then gx else gy)
  intro v
  simp
  apply Iff.intro <;> intro h
  . have ⟨v', hv'⟩ := h
    match v' with
    | 0 => left; simp at *; apply (hx _).mp hv'
    | 1 => right; simp at *; apply  (hy _).mp hv'
  . match h with
    | .inl h => exists 0; simp; exact (hx _).mpr h
    | .inr h => exists 1; simp; exact (hy _).mpr h

abbrev synth_unfoldM
    {α β : Type}
    {f : α → β → Option β}
    {b z : β}
    (g : (b : β) → CGen (ListF.rec (b = z) (λ a b' => f a b' = some b))) :
    CGen (λ v => List.foldrM f z v = .some b) := by
  exists (.sized (λ n => unfoldr' n (λ b => (g b).val) b))
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
    CGen (λ v => List.accu st f z v s = b) := by
  exists (.sized (λ n => unfoldr' n (λ (b, s) => do
    match (← (g b s).val) with
    | .nil => pure .nil
    | .cons x b' => pure (.cons x (b', st x s))) (b, s)))
  rw [support_unfoldr']
  simp_all
  intro v
  rw [←foldr_accu]
  on_goal 2 => exact Eq.refl _
  induction v generalizing s b with
  | nil =>
    have := (g b s).property .nil
    aesop
  | cons x xs ih =>
    have := (g b s).property (.cons x (List.foldr (fun x b s => f x (b (st x s)) s) z xs (st x s)))
    aesop

abbrev synth_accuM
    {α β σ : Type}
    {st : α → σ → σ}
    {f : α → β → σ → Option β}
    {z : σ → Option β}
    {s : σ}
    {b : β}
    (g : (b : β) → (s : σ) → CGen (ListF.rec (z s = some b) (λ a b' => f a b' s = some b))) :
    CGen (λ v => List.accuM st f z v s = some b) := by
  exists (.sized (λ n => unfoldr' n (λ (b, s) => do
    match (← (g b s).val) with
    | .nil => pure .nil
    | .cons x b' => pure (.cons x (b', st x s))) (b, s)))
  rw [support_unfoldr']
  simp_all
  intro xs
  rw [←foldr_accuM]
  on_goal 2 => exact Eq.refl _
  induction xs generalizing s b with
  | nil =>
    have := (g b s).property .nil
    aesop
  | cons x xs ih =>
    simp_all
    clear ih
    aesop (config := {warnOnNonterminal := false})
    . have := (g b s).property
      simp_all
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
        . exists .cons x b'
        . rw [ho]

abbrev synth_accuTreeM
    {α β σ : Type}
    {st : α → σ → σ × σ}
    {f : β → α → β → σ → Option β}
    {z : σ → Option β}
    {s : σ}
    {b : β}
    (g : (b : β) → (s : σ) → CGen (TreeF.rec (z s = some b) (λ bl a br => f bl a br s = some b))) :
    CGen (λ v => Tree.accuM st f z v s = some b) := by
  exists (.sized (λ n => unfoldTree n (λ (b, s) => do
    match (← (g b s).val) with
    | .leaf => pure .leaf
    | .node bl x br =>
      let (sl, sr) := st x s
      pure (.node (bl, sl) x (br, sr))) (b, s)))
  rw [support_unfoldTree_ok]
  simp_all
  intro t
  induction t generalizing s b with
  | leaf =>
    have := (g b s).property .leaf
    aesop (add simp Tree.accuM)
  | node l x r ih =>
    simp_all
    clear ih
    aesop
      (config := {warnOnNonterminal := false})
      (add simp Tree.accuM)
    . have := (g b s).property
      simp_all
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
          simp_all
          exists (.node bl x br)

abbrev synth_true
    [Arbitrary α] :
    CGen (λ (_ : α) => True) := by
  obtain ⟨g, p⟩ := @Arbitrary.arbitrary α _
  exists g

abbrev synth_between
    {lo hi : Nat} :
    CGen (λ v => lo ≤ v ∧ v ≤ hi) := by
  exists (if h : lo ≤ hi then .choose lo hi h else .fail)
  intro v
  simp_all
  by_cases hle : lo ≤ hi
  . aesop
  . split
    . simp_all
    . simp_all
      intro h'
      rename_i h''
      exact Nat.lt_of_lt_of_le h'' h'
