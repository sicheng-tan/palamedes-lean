inductive W {α : Type _} (β : α → Type _)
  | mk (a : α) (f : β a → W β) : W β

def W.elim {γ : Type _} (fγ : (Σa : α, β a → γ) → γ) : W β → γ
  | ⟨a, f⟩ => fγ ⟨a, fun b => elim fγ (f b)⟩

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
