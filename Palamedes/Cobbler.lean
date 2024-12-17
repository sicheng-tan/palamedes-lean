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

@[simp]
def synth_fn
    {q : α → β}
    {h : (x : α) → {p' : β // p' = q x}} :
    {p : α → β // ∀ x, p x = q x} := by
  exists λ x => h x
  intro x
  exact (h x).property

@[simp]
def synth_fn2
    {q : α → β → γ}
    {h : (x : α) → (y : β) → {p' : γ // p' = q x y}} :
    {p : α → β → γ // ∀ x y, p x y = q x y} := by
  exists λ x y => h x y
  intro x y
  exact (h x y).property

def synthesized_program1 :
    {p : (Int → Int) → Option Int → Int // ∀ f mx, p f mx = ex1_main f mx} := by
  apply synth_fn2
  intro f mx
  refine ⟨withDefault ?a (Option.map (?b : Int → Int) ?c), ?proof⟩
  case proof =>
    simp [Option.map, Option.getD]
    unfold Option.getD.match_1
    unfold ex1_main.match_1
    rw [deforest_option]
    exact Eq.refl _

@[simp]
def ex2_main (p : Int → Bool) (f : Int → Int) (xs : List Int) : List Int :=
  match xs with
  | [] => []
  | hd :: tl =>
    if p hd then f (f hd) :: ex2_main p f tl else ex2_main p f tl

example :
    ex2_main p f xs =
    List.map (λ x => f (f x)) (List.filter p xs) := by
  induction xs <;> aesop

def synth_fn3
    {q : α₁ → α₂ → α₃ → β}
    {h : (x : α₁) → (y : α₂) → (z : α₃) → {p' : β // p' = q x y z}} :
    {p : α₁ → α₂ → α₃ → β // ∀ x y z, p x y z = q x y z} := by
  exists λ x y z => h x y z
  intro x y z
  exact (h x y z).property

theorem map_foldr :
  List.map f xs = List.foldr (λ x xs => f x :: xs) [] xs := by
  induction xs <;> aesop

theorem filter_foldr :
  List.filter f xs = List.foldr (λ x xs => if f x then x :: xs else xs) [] xs := by
  induction xs <;> aesop

def synthesized_program2 :
    {p : (Int → Bool) → (Int → Int) → List Int → List Int // ∀ pred f xs, p pred f xs = ex2_main pred f xs} := by
  apply synth_fn3
  intro pred f xs
  refine ⟨List.map (?a : Int → Int) (List.filter ?b ?c), ?proof⟩
  case proof =>
    delta List.map
    delta List.filter
    delta ex2_main
    simp
    -- TODO: Implement deforestation
    all_goals sorry
  all_goals sorry
