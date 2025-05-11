import Palamedes.Support

inductive ListF (α β : Type) where
  | nil : ListF α β
  | cons : (a : α) → (b : β) → ListF α β

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

private def List.unfoldr_aux (n : Nat) (f : β → Gen (ListF α β)) (b : β) : Gen (Option (List α)) :=
  match n with
  | 0 => pure none
  | n + 1 => do
    match (← f b) with
    | .nil => pure (some [])
    | .cons x b' => .map (x :: .) <$> List.unfoldr_aux n f b'

attribute [local simp]
  bind
  optBind_bind
in
theorem unfoldr_aux_monotonic :
    some v ∈ 〚List.unfoldr_aux n f b〛 →
    some v ∈ 〚List.unfoldr_aux (n + 1) f b〛 := by
  induction n generalizing v f b
  case zero =>
    simp [List.unfoldr_aux]
  case succ n' ih =>
    unfold List.unfoldr_aux
    simp
    intro l hl hv
    exists l
    apply And.intro hl
    cases l <;> simp_all [Functor.map, Option.map]
    aesop

def List.unfoldr (f : β → Gen (ListF α β)) (b : β) : Gen (List α) :=
  .indexed (λ n => List.unfoldr_aux n f b)

@[simp]
def List.unfoldr_support (P : β → ListF α β → Prop) (b : β) (xs : List α) : Prop :=
  match xs with
  | [] => P b .nil
  | x :: xs => ∃ b', P b (.cons x b') ∧ List.unfoldr_support P b' xs

attribute [local simp]
  Bind.bind
  List.unfoldr
  List.unfoldr_aux
  Functor.map
  optBind_bind
in
theorem support_unfoldr :
    support (List.unfoldr f b) = List.unfoldr_support (λ b' => support (f b')) b := by
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

theorem ListF_or
    {α β : Type}
    {P : Prop}
    {Q : α → β → Prop}
    {t : ListF α β} :
    ListF.rec P Q t ↔ (P ∧ t = .nil) ∨ (∃ x b, t = .cons x b ∧ Q x b) := by
  match t with
  | .nil => simp
  | .cons x b => aesop

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

theorem coerce_to_foldr
    {xs : List α}
    {f : List α → β}
    {x : β}
    {g : α → β → β}
    (h1 : f [] = x)
    (h2 : ∀ x xs, f (x :: xs) = g x (f xs)) :
    f xs = xs.foldr g x := by
  induction xs <;> simp_all

theorem coerce_to_foldrM
    {xs : List α}
    {f : List α → Bool}
    {p : α → Bool}
    (h1 : f [] = true)
    (h2 : ∀ x xs, f (x :: xs) = (p x && f xs)) :
    (f xs = true) = (xs.foldrM (λ x () => guard (p x)) () = some ()) := by
  induction xs with
  | nil => simp [h1]
  | cons x xs ih =>
    simp [h2, List.foldrM_cons]
    match hfoldrM : List.foldrM (fun x x_1 => guard (p x = true)) () xs with
    | none => simp_all
    | some v => simp_all [guard]

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
