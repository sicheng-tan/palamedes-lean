import Palamedes.Support
import Mathlib.Logic.Equiv.Basic

@[pp_with_univ]
class Traversable.{v, u} (t : Type u → Type u) extends Functor t : Type (max (u + 1) (v + 1)) where
  -- Previously `m` was constrained to have type `Type u → Type u`
  traverse : ∀ {m : Type u → Type v} [Monad m] {α β}, (α → m β) → t α → m (t β)

inductive ListF (α β : Type) where
  | nil : ListF α β
  | cons : (a : α) → (b : β) → ListF α β

def iter (n : Nat) (f : α → α) : α → α :=
  match n with
  | 0 => id
  | m + 1 => f ∘ iter m f

abbrev Fix (f : Type → Type) := Σ n, iter n f Empty

def toFix : List α → Fix (ListF α)
  | [] => ⟨1, .nil⟩
  | x :: xs =>
    let ⟨n, xs'⟩ := toFix xs
    ⟨n + 1, .cons x xs'⟩

def ofFix : Fix (ListF α) → List α
  | ⟨1, .nil⟩ => []
  | ⟨_ + 1, .nil⟩ => []
  | ⟨n + 1, .cons x xs⟩ => x :: ofFix ⟨n, xs⟩

theorem left_inverse : ofFix (toFix xs) = xs := by
  induction xs with
  | nil => simp [toFix, ofFix]
  | cons x xs ih => simp [toFix, ofFix]; apply ih

def Fix.fold [Functor f] (alg : f β → β) : Fix f → β
  | ⟨n + 1, x⟩ => alg ((Fix.fold alg ⟨n, ·⟩) <$> x)

instance {α} : Functor (ListF α) where
  map :=
    λ f t =>
      match t with
      | .nil => .nil
      | .cons x xs => .cons x (f xs)

instance {α} : Traversable (ListF α) where
  traverse :=
    λ f t =>
      match t with
      | .nil => pure .nil
      | .cons x xs => .cons x <$> f xs

open Traversable in
def Fix.unfold
    [Traversable.{0} t]
    [Traversable.{1} t]
    (coalg : β → Gen (t β)) :
    β → Gen (Fix t) :=
  let rec go (b : β) (n : Nat) : Gen (Option (iter n t Empty)) :=
    match n with
    | 0 => pure none
    | n' + 1 => do
      let x ← coalg b
      let res? ← traverse id <$> traverse (λ b' => go b' n') x
      pure res?
  (λ b => .indexed (λ n => do
    match (← go b n) with
    | some x => pure (some ⟨n, x⟩)
    | none => pure none))

def unfoldr'' (n : Nat) (f : β → Gen (ListF α β)) (b : β) : Gen (Option (Fix (ListF α))) :=
  match n with
  | 0 => pure none
  | n + 1 => do
    match (← f b) with
    | .nil => pure (some ⟨1, .nil⟩)
    | .cons x b' =>
      match (← unfoldr'' n f b') with
      | none => pure none
      | some ⟨m, xs⟩ => pure (some ⟨m + 1, .cons x xs⟩)

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

theorem Fix_unfold_go_fold
    [Traversable.{0} t]
    [Traversable.{1} t]
    {alg : t β → β}
    {coalg : β → Gen (t β)}
    (h_coalg_alg : ∀ {xs} {b}, xs ∈ 〚coalg b〛 ↔ alg xs = b) :
    some v ∈ 〚Fix.unfold.go coalg b n〛 ↔ Fix.fold alg ⟨n, v⟩ = b := by
  induction n with
  | zero => contradiction
  | succ n' ih =>
    simp [Fix.unfold.go, Fix.fold, bind, optBind_bind]
    apply Iff.intro <;> intro h
    . replace ⟨v', h_coalg, h_unfold⟩ := h
      rw [← h_coalg_alg.mp h_coalg]
      congr
      sorry
    . sorry

theorem Fix_unfold_fold
    [Traversable.{0} t]
    [Traversable.{1} t]
    {alg : t β → β}
    {coalg : β → Gen (t β)}
    (h_coalg_alg : ∀ {xs} {b}, xs ∈ 〚coalg b〛 ↔ alg xs = b) :
    v ∈ 〚Fix.unfold coalg b〛 ↔ Fix.fold alg v = b := by
  apply Iff.intro <;> intro h
  . replace ⟨n, h⟩ := h
    simp [bind, optBind_bind] at h
    replace ⟨v', h⟩ := h
    cases v' <;> simp at h; case some v' =>
    obtain ⟨h, rfl⟩ := h
    exact (Fix_unfold_go_fold h_coalg_alg).mp h
  . simp [bind, optBind_bind]
    let ⟨n, v'⟩ := v
    exists n
    exists v'
    simp
    exact (Fix_unfold_go_fold h_coalg_alg).mpr h

-- example
--     {α β : Type}
--     (g : (b : β) → CGen (ListF.rec (b = z) (λ a b' => f a b' = some b))) :
--     CGen (λ v => Fix.foldr f z v = .some b) :=
--   Subtype.mk (List.unfoldr (λ b => (g b).val) b) <| by

-- def Traversable.all [Traversable.{0} t] : t Prop → Prop := sorry

-- @[simp]
-- def support_unfoldr (P : ListF α β → β → Prop) (xs : Fix (ListF α)) : β → Prop :=
--   xs.fold λ
--     | .nil => λ b => ∃ l, l = .nil ∧ P l b
--     | .cons x rest => λ b => ∃ b', P (.cons x b') b ∧ Traversable.all ((· b') <$> ListF.cons x rest)

  -- match xs with
  -- | [] => P .nil b
  -- | x :: xs => ∃ b', P (.cons x b') b ∧ support_unfoldr P xs b'

def unfoldr' (n : Nat) (f : β → Gen (ListF α β)) (b : β) : Gen (Option (List α)) :=
  match n with
  | 0 => pure none
  | n + 1 => do
    match (← f b) with
    | .nil => pure (some [])
    | .cons x b' => .map (x :: .) <$> unfoldr' n f b'

-- attribute [local simp] unfoldr' bind optBind_bind Functor.map Option.map in
-- theorem support_unfoldr' :
--     support (.sized (λ n => unfoldr' n f b)) = support_unfoldr (λ b' => support (f b')) b := by
--   funext xs
--   induction xs generalizing b with
--   | nil =>
--     simp_all
--     apply Iff.intro
--     . intro ⟨n, h⟩
--       cases n <;> aesop
--     . intro h
--       exists 1
--       simp
--       exists .nil
--   | cons x xs ih =>
--     simp_all
--     apply Iff.intro
--     . intro ⟨n, h⟩
--       match n with
--       | 0 => simp_all
--       | n + 1 =>
--         simp_all
--         have ⟨v', _, _⟩ := h
--         match v' with
--         | .nil => simp_all
--         | .cons _ b'' =>
--           aesop (config := {warnOnNonterminal := false})
--           exists b''
--           simp_all
--           apply (@ih b'').mp
--           exists n
--     . intro ⟨b', hx, hxs⟩
--       have ⟨n, h⟩ := ih.mpr hxs
--       exists n + 1
--       simp_all
--       exists ListF.cons x b'
--       simp_all
--       exists some xs

-- attribute [local simp] unfoldr'' bind optBind_bind Functor.map Option.map ofFix in
-- theorem support_unfoldr'' :
--     support (ofFix <$> .sized (λ fuel => unfoldr'' fuel f b)) =
--     support_unfoldr (λ b' => support (f b')) b := by
--   funext xs
--   induction xs generalizing b with
--   | nil =>
--     simp_all
--     apply Iff.intro
--     . intro ⟨_, _, ⟨fuel, h⟩, h'⟩
--       cases fuel <;> aesop
--     . intro h
--       exists 1
--       exists .nil
--       simp
--       exists 1
--       simp
--       exists .nil
--   | cons x xs ih =>
--     simp_all
--     apply Iff.intro
--     . intro ⟨_, _, ⟨fuel, h⟩, h'⟩
--       match fuel with
--       | 0 => simp_all
--       | fuel' + 1 =>
--         simp_all
--         have ⟨v', _, _⟩ := h
--         match v' with
--         | .nil => aesop
--         | .cons _ b'' =>
--           aesop (config := {warnOnNonterminal := false})
--           exists b''
--           simp_all
--           apply (@ih b'').mp
--           exists m
--           exists xs_1
--           simp
--           exists fuel'
--     . intro ⟨b', hx, hxs⟩
--       have ⟨n, xs', ⟨fuel, hxs'⟩, htrans⟩ := ih.mpr hxs
--       clear hxs
--       exists n + 1
--       exists ListF.cons x xs'
--       simp_all
--       exists fuel + 1
--       simp
--       exists ListF.cons x b'
--       simp_all
--       exists some ⟨n, xs'⟩
