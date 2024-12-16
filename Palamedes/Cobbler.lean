import Aesop

@[simp]
def withDefault : α → Option α → α := λ x y =>
  Option.getD y x

@[simp]
def ex1_main (f : Int → Int) (mx : Option Int) :=
  match mx with
  | .none => 0
  | .some x => f (f x)

example :
    ex1_main f mx =
    withDefault 0 (.map (λ x => f (f x)) mx) := by
  aesop

-- @[aesop safe constructors]
-- inductive Syntax : Type → Type 1 where
--   | map {α : Type} : (α → α) → Option α → Syntax (Option α)
--   | withDefault {α : Type} : α → Syntax (Option α) → Syntax α

-- @[simp]
-- def interp : Syntax α → α
--   | .map f x => Option.map f x
--   | .withDefault a o => withDefault a (interp o)

theorem deforest_option
    {α β γ : Type}
    {mx : Option α}
    {a : α → Option β}
    {b : Option β}
    {c : β → γ}
    {d : γ} :
    (Option.casesOn (Option.casesOn mx b a) d c : γ) =
    Option.casesOn mx
      (Option.casesOn b d c)
      (λ x => Option.casesOn (a x) d c) := by
  match mx with
  | .none => simp
  | .some x => simp

attribute [local simp] Option.map Option.getD in
def foo
    (f : Int → Int)
    (mx : Option Int) :
    {p : (Int → Int) → Option Int → Int // p f mx = ex1_main f mx} := by
  refine ⟨λ f mx =>
    Option.getD (Option.map (?b : Int → Int) ?c) ?a,
    ?proof⟩
  case proof =>
    simp
    unfold Option.getD.match_1
    unfold ex1_main.match_1
    rw [deforest_option]
    simp
    exact Eq.refl _

@[simp]
def ex2_main (p : Int → Bool) (f : Int → Int) (xs : List Int) :=
  match xs with
  | [] => []
  | hd :: tl =>
    if p hd then f (f hd) :: ex2_main p f tl else ex2_main p f tl

example :
    ex2_main p f xs =
    List.map (λ x => f (f x)) (List.filter p xs) := by
  induction xs <;> aesop
