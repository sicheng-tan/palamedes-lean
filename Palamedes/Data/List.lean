import Palamedes.Support

/- Base functor -/

inductive ListF (α β : Type) where
  | nil : ListF α β
  | cons : (a : α) → (b : β) → ListF α β

theorem ListF_or
    {α β : Type}
    {P : Prop}
    {Q : α → β → Prop}
    {t : ListF α β} :
    ListF.rec P Q t ↔ (P ∧ t = .nil) ∨ (∃ x b, t = .cons x b ∧ Q x b) := by
  match t with
  | .nil => simp
  | .cons x b => aesop

/- Recursion schemes -/

@[simp]
def List.fold {α β: Type} (f : α → β → β) (z : β) (xs : List α)
  := List.foldr f z xs

@[simp] theorem List.fold_nil : List.fold f z .nil = z := rfl
@[simp] theorem List.fold_cons {x} {xs : List α} {f : α → β → β} {z} :
    List.fold f z (.cons x xs) = f x (List.fold f z xs) := rfl

def List.accuM
    [Monad m]
    {α β σ : Type}
    (st : α → σ → σ)
    (f : α → β → σ → m β)
    (z : σ → m β)
    (xs : List α)
    (s : σ) :
    m β :=
  match xs with
  | [] => z s
  | x :: xs => do f x (← List.accuM st f z xs (st x s)) s


@[simp] theorem List.accuM_nil [Monad m] {α} {st : α → σ → σ}
  {f : α → β → σ → m β} {z : σ → m β} {i : σ} : List.accuM st f z .nil i = z i := rfl
@[simp] theorem List.accuM_cons  [Monad m] {α} {st : α → σ → σ}
  {f : α → β → σ → m β} {z : σ → m β} {i : σ}  {z} {x} {xs : List α} :
    List.accuM st f z (.cons x xs) i = (do f x (← List.accuM st f z xs (st x i)) i) := rfl

/- Unfold -/

private def List.unfold_aux (n : Nat) (f : β → Gen (ListF α β)) (b : β) : Gen (Option (List α)) :=
  match n with
  | 0 => pure none
  | n + 1 => do
    match (← f b) with
    | .nil => pure (some [])
    | .cons x b' => .map (x :: .) <$> List.unfold_aux n f b'

attribute [local simp]
  bind
  optBind_bind
in
theorem List.unfold_aux_monotonic :
    some v ∈ 〚List.unfold_aux n f b〛 →
    some v ∈ 〚List.unfold_aux (n + 1) f b〛 := by
  induction n generalizing v f b
  case zero =>
    simp [List.unfold_aux]
  case succ n' ih =>
    unfold List.unfold_aux
    simp
    intro l hl hv
    exists l
    apply And.intro hl
    cases l <;> simp_all [Functor.map, Option.map]
    aesop

def List.unfold (f : β → Gen (ListF α β)) (b : β) : Gen (List α) :=
  .indexed (λ n => List.unfold_aux n f b)

@[simp]
def List.unfold_support (P : β → ListF α β → Prop) (b : β) (xs : List α) : Prop :=
  match xs with
  | [] => P b .nil
  | x :: xs => ∃ b', P b (.cons x b') ∧ List.unfold_support P b' xs

attribute [local simp]
  Bind.bind
  List.unfold
  List.unfold_aux
  Functor.map
  optBind_bind
in
theorem List.unfold_support_ok :
    support (List.unfold f b) = List.unfold_support (λ b' => support (f b')) b := by
  funext xs
  simp_all
  induction xs generalizing b with
  | nil =>
    apply Iff.intro
    . intro ⟨n, h⟩
      cases n <;> simp_all
      have ⟨v', hv'1, hv'2⟩ := h
      cases v' <;> simp_all
      have ⟨v'', hv''⟩ := hv'2
      cases v'' <;> simp_all
    . aesop (add unsafe (by exists 1))
  | cons x xs ih =>
    apply Iff.intro
    . intro ⟨n, h⟩
      cases n <;> simp_all; case succ n =>
      have ⟨v', hv'1, hv'2⟩ := h
      cases v' <;> simp_all
      case cons _ b'' =>
      have ⟨v'', hv''⟩ := hv'2
      cases v'' <;> simp_all
      obtain ⟨hv'', rfl, rfl⟩ := hv''
      exists b''
      apply And.intro hv'1
      apply (@ih b'').mp
      exists n
    . intro ⟨b', hx, hxs⟩
      have ⟨n, h⟩ := ih.mpr hxs
      exists n + 1
      simp_all
      exists ListF.cons x b'
      simp_all
      exists some xs

/- Fold special cases -/

theorem List.fold_accu_Option_basic
    {α β : Type}
    {v : β}
    {xs : List α}
    {z : β}
    {f : α → β → β} :
    List.fold f z xs = v ↔
    List.accuM
      (fun _ _ => ())
      (fun x xs _ => some (f x xs))
      (fun _ => some z)
      xs
      () = some v := by
    induction xs generalizing v <;> simp_all [List.fold, List.accuM]
    case cons x xs' ih =>
      replace ih := @ih (List.fold f z xs')
      simp_all [List.fold, List.accuM]

theorem List.fold_accu_Option_true
    {α : Type}
    {xs : List α}
    {g : α → Bool}
    {f :  α → Bool → Bool}
    (h : ∀ x acc, f x acc = (g x && acc)) :
    List.fold f true xs = true ↔
    List.accuM
      (fun _ _ => ())
      (fun x _ _ => guard (g x))
      (fun _ => some ())
      xs
      () = some () := by
    induction xs <;> simp_all [List.fold, List.accuM]
    case cons x xs' ih =>
        apply Iff.intro <;> intro hf
        . -- (->)
          generalize hv : fold f true xs' = v
          cases v <;>
            simp_all [List.fold, List.accuM, guard]
        . -- (<-)
          rw [Option.bind_eq_some] at hf
          replace ⟨ v, hf ⟩ := hf
          simp_all [List.fold, List.accuM, guard]

theorem List.fold_accu_Option_function
    {α β σ : Type}
    {i : σ}
    {v : β}
    {xs : List α}
    {z : (σ → β)}
    {f : α → (σ → β) → (σ → β)}
    {g : α → β → σ → Option β}
    {st :  α → σ → σ}
    (h : ∀ x acc s,
      f x acc s = v ↔ (do g x (← acc (st x s)) s) = some v)
    :
    List.fold f z xs i = v ↔
    List.accuM
      st
      g
      (fun s => some (z s))
      xs
      i = some v := by
    induction xs generalizing v i <;> simp_all [List.fold, List.accuM, Option.bind_eq_some]
    case cons x xs' ih =>
      apply Iff.intro <;> intro hg
      . -- (->)
        exists (List.fold f z xs' (st x i))
        simp_all
        sorry
      . -- (<-)
        replace ⟨v', ⟨hg', hg⟩⟩ := hg
        sorry

theorem List.fold_accu_Option_function_true
    {α σ : Type}
    {i : σ}
    {xs : List α}
    {f : α → (σ → Bool) → (σ → Bool)}
    {g : α → σ → Bool}
    {st :  α → σ → σ}
    (h : ∀ x acc s,
      f x acc s = true ↔ (do (return (g x s) && (← acc (st x s)))) = some true)
    :
    List.fold f (λ _ => true) xs i = true ↔
    List.accuM
      st
      (fun x _ s => guard $ g x s)
      (fun _ => some ())
      xs
      i = some () := by
    induction xs generalizing i <;> simp_all [List.fold, List.accuM, Option.bind_eq_some, guard]
    case cons x xs' ih =>
      apply Iff.intro <;> intro hg <;> simp_all
      replace ⟨⟨v, hv ⟩ , hg⟩ := hg <;> simp_all

/- Conversion of recursive functions to fold -/

theorem List.coerce_to_fold
    {xs : List α}
    {f : List α → β}
    {z : β}
    {g : α → β → β}
    (h1 : f [] = z)
    (h2 : ∀ x xs, f (x :: xs) = g x (f xs)) :
    f xs = xs.fold g z := by
  induction xs <;> simp_all

/- Merging two accumulators -/
theorem List.merge_accuM
    {xs : List α}
    {st₁ : α → σ₁ → σ₁}
    {st₂ : α → σ₂ → σ₂}
    {f₁ : α → β₁ → σ₁ → Option β₁}
    {f₂ : α → β₂ → σ₂ → Option β₂}
    {s₁ : σ₁} {s₂ : σ₂}
    {z₁ : σ₁ → Option β₁} {z₂ : σ₂ → Option β₂}
    {b₁ : β₁} {b₂ : β₂}
    :
    (xs.accuM st₁ f₁ z₁ s₁ = some b₁ ∧ xs.accuM st₂ f₂ z₂ s₂ = some b₂)
    ↔
    (xs.accuM
      (λ x (s₁, s₂) => (st₁ x s₁, st₂ x s₂))
      (λ x (b₁, b₂) (s₁, s₂) => do (← f₁ x b₁ s₁, ← f₂ x b₂ s₂))
      (λ (s₁, s₂) => do (← z₁ s₁, ← z₂ s₂))
      (s₁, s₂) = some (b₁, b₂)) := by
    induction xs generalizing st₁ st₂ f₁ f₂ s₁ s₂ z₁ z₂ b₁ b₂
    case nil => simp_all [List.accuM, Option.bind_eq_some]
    case cons y ys ih =>
      simp_all [List.accuM, Option.bind_eq_some]
      apply Iff.intro
      . -- (->)
        intro ⟨ ⟨ v₁, ⟨ hv1h, hv1tl ⟩ ⟩ , ⟨ v₂, ⟨ hv2h, hv2tl ⟩ ⟩ ⟩
        exists v₁, v₂
        replace ih := @ih st₁ st₂ f₁ f₂ (st₁ y s₁) (st₂ y s₂) z₁ z₂ v₁ v₂
        simp_all [List.accuM, Option.bind_eq_some]
      . -- (<-)
        intro ⟨ v₁, v₂, h, h1, h2 ⟩
        replace ih := @ih st₁ st₂ f₁ f₂ (st₁ y s₁) (st₂ y s₂) z₁ z₂ v₁ v₂
        apply And.intro
        . exists v₁
          simp_all [List.accuM, Option.bind_eq_some]
        . exists v₂
          simp_all [List.accuM, Option.bind_eq_some]

/-
TODO: we can probably remove these

theorem coerce_to_accuM
    {xs : List α}
    {f : List α → σ → Bool}
    {p : α → σ → Bool}
    {t : α → σ → σ}
    (h₁ : ∀ s, f [] s = true)
    (h₂ : ∀ x xs s, f (x :: xs) s = (p x s && f xs (t x s))) :
    (f xs s = true) = (xs.accuM t (λ x () s => guard (p x s)) (λ _ => some ()) s = some ()) := by
  induction xs generalizing s with
  | nil => simp [List.accuM, h₁]
  | cons x xs ih =>
    simp [List.accuM, h₂]
    apply Iff.intro
    . aesop
    . intro h
      simp_all [Option.bind, guard]
      aesop

def List.accu
    {α β σ : Type}
    (st : α → σ → σ)
    (f : α → β → σ → β)
    (z : σ → β)
    (xs : List α)
    (s : σ) :
    β :=
  match xs with
  | [] => z s
  | x :: xs => f x (List.accu st f z xs (st x s)) s

theorem fold_accu
    {α β σ : Type}
    {st : α → σ → σ}
    {s : σ}
    {xs : List α}
    {z : σ → β}
    {f : α → β → σ → β}
    {f' : α → (σ → β) → σ → β} :
    f' = (λ x b => λ s => f x (b (st x s)) s) →
    List.fold f' z xs s = List.accu st f z xs s := by
  induction xs generalizing s <;> simp_all [List.accu]


theorem fold_foldM
    {α β : Type}
    {f : α → β → β}
    {z b : β}
    {xs : List α} :
    List.fold f z xs = b ↔ List.foldM (λ x b => Option.some (f x b)) z xs = Option.some b := by
  induction xs generalizing b with
  | nil => simp_all
  | cons x xs ih =>
    simp_all only [List.fold_cons, List.foldM_cons, Option.bind_eq_bind]
    apply Iff.intro
    · intro a
      subst a
      generalize List.foldM (fun x b => some (f x b)) z xs = o at *
      match o with
      | .none => simp_all
      | .some v =>
        simp_all
        rw [ih.mp]
        simp
    · intro a
      generalize List.foldM (fun x b => some (f x b)) z xs = o at *
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
    (List.foldM f₁ z₁ xs = some b₁ ∧ List.foldM f₂ z₂ xs = some b₂) ↔
    List.foldM (λ x b => do (← f₁ x b.fst, ← f₂ x b.snd)) (z₁, z₂) xs = some (b₁, b₂) := by
  induction xs generalizing b₁ b₂ with
  | nil => simp_all
  | cons x xs ih =>
    simp_all
    apply Iff.intro
    . intro h
      generalize List.foldM f₁ z₁ xs = mx₁ at *
      generalize List.foldM f₂ z₂ xs = mx₂ at *
      match mx₁, mx₂ with
      | .none, _ => simp_all
      | _, .none => simp_all
      | .some x₁, .some x₂ =>
        rw [(@ih x₁ x₂).mp (by simp_all)]
        simp_all
    . intro h
      generalize List.foldM
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

theorem coerce_to_foldM
    {xs : List α}
    {f : List α → Bool}
    {p : α → Bool}
    (h1 : f [] = true)
    (h2 : ∀ x xs, f (x :: xs) = (p x && f xs)) :
    (f xs = true) = (xs.foldM (λ x () => guard (p x)) () = some ()) := by
  induction xs with
  | nil => simp [h1]
  | cons x xs ih =>
    simp [h2, List.foldM_cons]
    match hfoldM : List.foldM (fun x x_1 => guard (p x)) () xs with
    | none => simp_all
    | some v => simp_all [guard]

theorem List.fold_accuM
    [Monad m]
    {α β σ : Type}
    {st : α → σ → σ}
    {s : σ}
    {xs : List α}
    {z : σ → m β}
    {f : α → β → σ → m β}
    {f' : α → (σ → m β) → σ → m β} :
    f' = (λ x b => λ s => do f x (← b (st x s)) s) →
    List.fold f' z xs s = List.accuM st f z xs s := by
  induction xs generalizing s <;> simp_all [List.accuM]

-/
