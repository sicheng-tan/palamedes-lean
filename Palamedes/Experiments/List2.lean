import Palamedes.Support
import Mathlib.Logic.Equiv.Basic

@[pp_with_univ]
class Traversable.{v, u} (t : Type u → Type u) extends Functor t : Type (max (u + 1) (v + 1)) where
  -- Previously `m` was constrained to have type `Type u → Type u`
  traverse : ∀ {m : Type u → Type v} [Monad m] {α β}, (α → m β) → t α → m (t β)

open Traversable

def iter (n : Nat) (f : α → α) : α → α :=
  match n with
  | 0 => id
  | m + 1 => f ∘ iter m f

abbrev Fix (f : Type → Type) := Σ n, iter n f Empty

def Fix.fold [Functor f] (alg : f β → β) : Fix f → β
  | ⟨n + 1, x⟩ => alg ((Fix.fold alg ⟨n, ·⟩) <$> x)

def Fix.foldM [Monad m] [Traversable t] (alg : t β → m β) : Fix t → m β
  | ⟨n + 1, x⟩ => do
    alg (← traverse (Fix.foldM alg ⟨n, ·⟩) x)

def Fix.unfoldM
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

-- theorem traverse1
--     [Monad f]
--     [Traversable t]
--     {x : t α} :
--   traverse id (pure <$> x) = (pure x : f (t α)) := sorry

-- theorem lemma1
--     [Traversable.{0} t]
--     [Traversable.{1} t]
--     {v' : t β}
--     {v : t α}
--     {f : β → Gen (Option α)}
--     (h : some v ∈ 〚traverse id <$> traverse f v'〛) :
--     ∀ b, ∃ v', some v' ∈ 〚f b〛 :=
--   sorry

theorem Fix_unfold_go_fold
    [Traversable.{0} t]
    [Traversable.{1} t]
    {alg : t β → β}
    {coalg : β → Gen (t β)}
    (h_coalg_alg : ∀ {xs} {b}, xs ∈ 〚coalg b〛 ↔ alg xs = b) :
    some v ∈ 〚Fix.unfoldM.go coalg b n〛 ↔ Fix.fold alg ⟨n, v⟩ = b := by
  induction n generalizing b with
  | zero => contradiction
  | succ n' ih =>
    simp [Fix.unfoldM.go, Fix.fold, bind, optBind_bind]
    apply Iff.intro <;> intro h
    . obtain ⟨v', h_coalg, h_unfold⟩ := h
      rw [← h_coalg_alg.mp h_coalg]
      clear h_coalg_alg
      congr
      sorry
    . sorry

theorem Fix_unfold_fold
    [Traversable.{0} t]
    [Traversable.{1} t]
    {alg : t β → β}
    {coalg : β → Gen (t β)}
    (h_coalg_alg : ∀ {xs} {b}, xs ∈ 〚coalg b〛 ↔ alg xs = b) :
    v ∈ 〚Fix.unfoldM coalg b〛 ↔ Fix.fold alg v = b := by
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

theorem Fix_unfold_foldM
    [Traversable.{0} t]
    [Traversable.{1} t]
    {alg : t β → Option β}
    {coalg : β → Gen (t β)}
    (h_coalg_alg : ∀ {xs} {b}, xs ∈ 〚coalg b〛 ↔ alg xs = some b) :
    v ∈ 〚Fix.unfoldM coalg b〛 ↔ Fix.foldM alg v = some b := by
  sorry

abbrev synth_unfold
    [Traversable.{0} t]
    [Traversable.{1} t]
    {alg : t β → Option β}
    (g : (b : β) → CGen (λ (v : t β) => alg v = some b)) :
    CGen (λ (v : Fix t) => Fix.foldM alg v = some b) :=
  Subtype.mk (Fix.unfoldM (λ b => (g b).val) b) <| by
    intro v
    apply Fix_unfold_foldM

    intro xs b
    have hg := (g b).property
    simp_all

theorem coerce_to_fold
    [Traversable.{0} t]
    {xs : Fix t}
    {f : Fix t → β}
    {alg : t β → β}
    (h : ∀ n x, f ⟨n + 1, x⟩ = alg ((f ⟨n, ·⟩) <$> x)) :
    f xs = xs.fold alg := by
  let ⟨n, x⟩ := xs
  induction n with
  | zero => contradiction
  | succ n' ih =>
    simp [Fix.fold, h]
    congr
    simp [ih]

inductive ListF (α β : Type) where
  | nil : ListF α β
  | cons : (a : α) → (b : β) → ListF α β

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

def toFix : List α → Fix (ListF α)
  | [] => ⟨1, .nil⟩
  | x :: xs =>
    let ⟨n, xs'⟩ := toFix xs
    ⟨n + 1, .cons x xs'⟩

def ofFix : Fix (ListF α) → List α
  | ⟨1, .nil⟩ => []
  | ⟨_ + 1, .nil⟩ => []
  | ⟨n + 1, .cons x xs⟩ => x :: ofFix ⟨n, xs⟩

theorem left_inverse {α : Type} {xs : List α} : ofFix (toFix xs) = xs := by
  induction xs with
  | nil => simp [toFix, ofFix]
  | cons x xs ih => simp [toFix, ofFix]; apply ih

def evenLength : List α → Bool
  | [] => true
  | _ :: xs => not (evenLength xs)

def evenLength' : Fix (ListF α) → Bool := Fix.fold alg
  where
    alg
      | .nil => true
      | .cons _ b => not b

example {α : Type} {xs : List α} : evenLength xs = evenLength' (toFix xs)  := by
  calc
    evenLength xs
      = evenLength (ofFix (toFix xs)) := by rw [left_inverse]
    _ = (evenLength ∘ ofFix) (toFix xs) := by rfl
    _ = evenLength' (toFix xs) := by
      apply coerce_to_fold
      intro n x
      cases n <;> cases x <;> simp [ofFix, evenLength, evenLength'.alg]

theorem List_foldr_Fix_fold
    {z : β}
    {xs : List α} :
    xs.foldr f z =
      (toFix xs).fold (fun | ListF.nil => z | .cons x b => f x b) := by
  induction xs generalizing z with
  | nil => simp [toFix, Fix.fold]
  | cons x xs ih => simp [toFix, Fix.fold, ih]

abbrev synth_unfold_List
    {alg : ListF α β → Option β}
    (g : (b : β) → CGen (λ (v : ListF α β) => alg v = some b)) :
    CGen (λ (v : List α) => Fix.foldM alg (toFix v) = some b) :=
  Subtype.mk (ofFix <$> Fix.unfoldM (λ b => (g b).val) b) <| by
    intro v
    have halg : ∀ {xs : ListF α β} {b : β}, xs ∈ 〚↑(g b)〛 ↔ alg xs = some b := by
      intro xs b
      have hg := (g b).property
      simp_all
    have := Fix_unfold_foldM (v := toFix v) (b := b) halg
    clear halg
    simp only [Functor.map, optBind_bind]
    rw [← this]
    clear this
    simp
    apply Iff.intro
    . intro ⟨a, b, ⟨⟨n, hn⟩, hb⟩⟩
      exists n
      subst hb
      simp_all [bind, optBind_bind]
      obtain ⟨v', hv'₁, hv'₂⟩ := hn
      exists v'
      apply And.intro hv'₁
      match v' with
      | none => simp_all
      | some v'' =>
        obtain ⟨rfl, rfl⟩ := hv'₂
        simp
        sorry -- FIXME: Needs right inverse
    . intro ⟨n, hn⟩
      match htoFixv : toFix v with
      | ⟨a, b⟩ =>
        exists a
        exists b
        apply And.intro
        . exists n
          aesop
        . have : ofFix (toFix v) = ofFix ⟨a, b⟩ := by simp [*]
          rw [← this]
          exact Eq.symm left_inverse
