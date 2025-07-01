import Palamedes.Synthesizer
import Batteries.Data.List.Lemmas

open Gen CorrectGen

theorem getElem?_eq_some_iff_indexesOf_getElem?_eq_some
    [BEq α]
    [LawfulBEq α]
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
      match i with
      | 0 => simp_all; exists 0
      | i' + 1 =>
        simp_all
        replace ⟨j, h⟩ := h
        by_cases hxa : x == a
        . simp_all
          exists j + 1
          simpa
        . have : (x == a) = false := by
            exact Eq.symm ((fun {a b} => Bool.not_not_eq.mp) fun a_1 => hxa (id (Eq.symm a_1)))
          simp [this]
          exists j
    . sorry
