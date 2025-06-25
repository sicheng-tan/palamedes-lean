import Palamedes.Synthesizer
import Batteries.Data.List.Lemmas

open Gen CorrectGen

@[reducible]
def elements (xs : List α) (h : xs.length > 0) : Gen α :=
  match xs with
  | x :: xs =>
    match xs with
    | [] => pure x
    | x' :: xs => pick (pure x) (elements (x' :: xs) (by simp_all))

def s_elements_partial {xs : List α} : CorrectGen (fun (a : α) => ∃ (i : Nat), xs[i]? = some a) :=
  Subtype.mk (assume (xs.length > 0) (fun h => elements xs (by simp_all))) <| by
    simp
    funext
    simp
    induction xs with
    | nil => simp_all
    | cons x xs ih =>
      match xs with
      | [] =>
        simp_all
        apply Iff.intro
        . intro h
          subst h
          exists 0
        . intro ⟨i, h⟩
          simp [List.getElem?_eq_some_iff] at h
          simp_all
      | x' :: xs =>
        simp_all
        apply Iff.intro
        . intro h
          match h with
          | .inl h => sorry
          | .inr h => sorry
        . intro ⟨i, h⟩
          match hi : i with
          | 0 => simp_all
          | n + 1 =>
            simp_all
            subst hi
            sorry

theorem getElem?_eq_some_iff_indexesOf_getElem?_eq_some
    [BEq α]
    {xs : List α}
    {i : Nat}
    {a : α} :
    xs[i]? = some a ↔ (∃ (j : Nat), (xs.indexesOf a)[j]? = some i) := by
  induction xs generalizing a i with
  | nil => simp [List.indexesOf_nil]
  | cons x xs ih =>
    simp [List.indexesOf_cons, List.getElem?_cons]
    apply Iff.intro
    . intro h
      sorry
    . sorry

example {xs : List Nat} {a : Nat} : CorrectGen (fun (i : Nat) => xs[i]? = some a) := by
  apply convert (by funext i; simp; apply (Iff.symm getElem?_eq_some_iff_indexesOf_getElem?_eq_some)) s_elements_partial
