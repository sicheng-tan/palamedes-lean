import Mathlib.Control.Traversable.Basic

inductive W {α : Type _} (β : α → Type _)
  | mk (a : α) (f : β a → W β) : W β

@[simp]
abbrev PFunctor {α : Type _} (β : α → Type) (γ : Type) : Type :=
  (Σ a : α, β a → γ)

@[simp]
def PFunctor.mk {α : Type _} {β : α → Type} (a : α) (f : β a → γ) : PFunctor β γ :=
  ⟨a, f⟩

instance : Functor (PFunctor β) where
  map := λ f fγ =>
    let ⟨a, g⟩ := fγ
    ⟨a, f ∘ g⟩

def W.elim {γ : Type _} (fγ : PFunctor β γ → γ) : W β → γ
  | ⟨a, f⟩ => fγ ⟨a, fun b => elim fγ (f b)⟩

theorem elim_eq
    {α γ : Type}
    {β : α → Type}
    {t : W β}
    {fγ : PFunctor β γ → γ}
    {r : γ} :
    W.elim fγ t = r ↔
    @W.elim _ _ (γ → Prop) (λ ⟨a, result⟩ => λ r =>
      ∃ (b' : β a → γ),
        fγ ⟨a, b'⟩ = r ∧
        ∀ (c : β a), result c (b' c)) t r := by
  induction t generalizing r with
  | mk a f ih =>
    simp_all
    apply Iff.intro <;> intro h
    . simp_all [W.elim]
      subst h
      exists fun b => W.elim fγ (f b)
      simp
      intro c
      apply (ih c).mp
      simp
    . simp_all [W.elim]
      obtain ⟨b', rfl, hb'⟩ := h
      congr
      funext x
      apply (ih _).mpr
      apply hb' x

def W.elimM
    [Monad m]
    [Traversable (PFunctor β)]
    {γ : Type _}
    (fγ : PFunctor β γ → m γ) :
    W β → m γ :=
  W.elim (λ t => sequence t >>= fγ)

inductive Natα : Type
  | zero : Natα
  | succ : Natα

def Natβ : Natα → Type
  | Natα.zero => Empty
  | Natα.succ => Unit

@[simp]
def ofNat : Nat → W Natβ
  | Nat.zero => ⟨Natα.zero, Empty.elim⟩
  | Nat.succ n => ⟨Natα.succ, λ () => ofNat n⟩

@[simp]
def toNat : W Natβ → Nat
  | W.mk Natα.zero _ => 0
  | W.mk Natα.succ f => (toNat (f ())).succ

inductive Listα : (α : Type) → Type where
  | nil : Listα α
  | cons : α → Listα α

def Listβ (α : Type) : Listα α → Type
  | Listα.nil => Empty
  | Listα.cons _ => Unit

@[simp]
def ofList : List α → W (Listβ α)
  | List.nil => ⟨Listα.nil, Empty.elim⟩
  | List.cons x xs => ⟨Listα.cons x, λ _ => ofList xs⟩

@[simp]
def toList : W (Listβ α) → List α
  | W.mk Listα.nil _ => []
  | W.mk (Listα.cons x) f => x :: toList (f ())

def Listβ.foldr (f : α → β → β) (z : β) : W (Listβ α) → β :=
  W.elim (λ ⟨a, result⟩ =>
    match a with
    | .nil => z
    | .cons x => f x (result ()))

inductive Treeα : (α : Type) → Type where
  | leaf : Treeα α
  | node : α → Treeα α

def Treeβ (α : Type) : Treeα α → Type
  | Treeα.leaf => Empty
  | Treeα.node _ => Fin 1

@[simp]
def Treeβ.fold (f : β → α → β → β) (z : β) : W (Treeβ α) → β :=
  W.elim (λ ⟨a, result⟩ =>
    match a with
    | .leaf => z
    | .node x => f (result (Fin.ofNat 0)) x (result (Fin.ofNat 1)))

instance : Traversable (PFunctor Natβ) where
  traverse := λ f ⟨a, result⟩ =>
    match a with
    | .zero => pure ⟨Natα.zero, Empty.elim⟩
    | .succ => Functor.map (λ y => ⟨Natα.succ, λ () => y⟩) (f (result ()))

instance : Traversable (PFunctor (Listβ α)) where
  traverse := λ f ⟨a, result⟩ =>
    match a with
    | .nil => pure ⟨Listα.nil, Empty.elim⟩
    | .cons x => Functor.map (λ y => ⟨Listα.cons x, λ () => y⟩) (f (result ()))

instance : LawfulFunctor (PFunctor (Listβ α)) where
  map_const := sorry
  id_map := sorry
  comp_map := sorry

instance : LawfulTraversable (PFunctor (Listβ α)) where
  id_traverse := by
    intro α x
    match x with
    | .mk .nil _ =>
      simp [traverse]
      congr
      conv =>
        rhs
        intro x
        tactic => contradiction
    | .mk (.cons x) f => simp [traverse]; congr
  comp_traverse := sorry
  traverse_eq_map_id := sorry
  naturality := sorry

theorem sequence_pfunctor_some
    {γ : Type}
    {F : Type → Type}
    [Functor F]
    [Traversable F]
    [LawfulTraversable F]
    (t : F (Option γ))
    (t' : F γ) :
    sequence t = Option.some t' ↔ t = Option.some <$> t' := by
  apply Iff.intro
  . intro h
    /-
    case mp
    ...
    h : sequence t = some t'
    ⊢ t = some <$> t'
    NOTE: Might not be true?
    -/
    sorry
  . intro h
    subst h
    rw [Eq.comm]
    /-
    case mpr
    ...
    ⊢ some t' = sequence (some <$> t')
    NOTE: Should follow by naturality?
    -/
    sorry

theorem sequence_pfunctor_some'
    {α γ : Type}
    {β : α → Type}
    [Traversable (PFunctor β)]
    [LawfulTraversable (PFunctor β)]
    (t : PFunctor β γ) :
    Option.some t = sequence (Option.some <$> t) := by
  rw [Eq.comm]
  apply (sequence_pfunctor_some (Option.some <$> t) t).mpr
  rfl

  -- let appSome := @ApplicativeTransformation.mk Id _ Option _ (λ (_ : Type) x => Option.some x) ?_ ?_
  -- have : (sequence : Id (PFunctor β γ) → (PFunctor β (Id γ))) t = t := by
  --   simp [sequence, traverse]
  -- conv =>
  --   lhs
  --   arg 1
  --   rw [←this]
  -- simp [sequence]
  -- have foo := LawfulTraversable.naturality appSome id t
  -- have : @Option.some = (λ {α} => appSome.app α) := by
  --   simp
  -- conv =>
  --   lhs
  --   rw [this]
 --
  --   let appSome := @ApplicativeTransformation.mk Id _ Option _ (λ (_ : Type) x => Option.some x) ?_ ?_
  -- have : ∀ (α : Type), @Option.some α = (λ _ x => Option.some x) α := by
  --   simp
  -- conv =>
  --   lhs
  --   rw [←LawfulTraversable.id_traverse t]
  --   rw [this]
  --   rw [LawfulTraversable.naturality appSome _ _]
  -- have :
  --   (Option.some <$> t : PFunctor β (Option γ)) =
  --   traverse ((pure : Option γ → Id (Option γ)) ∘ Option.some) t := by
  --   sorry
  -- conv =>
  --   rhs
  --   simp [sequence]
  --   arg 2

theorem sequence_pfunctor_option_injective
    {α γ : Type}
    {β : α → Type}
    [Traversable (PFunctor β)]
    [LawfulTraversable (PFunctor β)]
    {t t' : PFunctor β (Option γ)} :
    sequence t = sequence t' →
    sequence t = none ∨ t = t' := by
  intro h
  match hsome : sequence t with
  | .none => left; simp
  | .some t'' =>
    right
    rw [hsome] at h
    rw [Eq.comm] at h
    rw [(sequence_pfunctor_some _ _).mp h]
    rw [(sequence_pfunctor_some _ _).mp hsome]
