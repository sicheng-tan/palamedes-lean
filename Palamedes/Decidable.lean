/-
Lemmas for rewriting terms with `if` that compile to matches on Decidable P for
some Prop P.
-/

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
