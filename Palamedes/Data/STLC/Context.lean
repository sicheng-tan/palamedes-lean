import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Total

open Gen CorrectGen

def elements (xs : List α) (h : xs.length > 0) : Gen α :=
  match xs with
  | x :: xs =>
    match hxs : xs with
    | [] => pure x
    | _ :: _ => pick (pure x) (elements xs (by rw [hxs]; simp))

@[simp]
theorem support_elements
    {xs : List α} {v : α} {h : xs.length > 0} :
    v ∈ 〚elements xs h〛↔ v ∈ xs := by
  induction xs with
  | nil => simp_all; contradiction
  | cons x xs ih =>
    match hxs : xs with
    | [] =>
      simp_all [elements]
    | _ :: _ =>
      simp [elements] at ih |-
      simp_all [support]

@[reducible]
def s_elements_partial [DecidableEq α] (xs : List α) : CorrectGen (λ v => List.elem v xs) :=
  Subtype.mk (assume (xs.length > 0) (λ h => elements xs (by aesop))) <| by
    funext v
    simp [support_elements]
    cases xs <;> simp_all

@[reducible]
def indicesOf [DecidableEq α] (xs : List α) (a : α) : Gen Nat :=
  let inds := (xs.enum.filter (λ (_, x) => x == a)).map (λ (n, _) => n)
  .assume (inds.length > 0)
          (λ h => elements inds (by simp_all only [decide_eq_true_eq]))

@[reducible]
def s_indicesOf [DecidableEq α] (xs : List α) (a : α) : CorrectGen (λ (n : Nat) => xs[n]? = some a) :=
  Subtype.mk (indicesOf xs a) <| by
  funext v
  simp
  sorry

@[reducible]
def indicesOf' [DecidableEq α] (xs : List α) (a : α) : Gen Nat :=
  let inds := List.indexesOf a xs
  .assume (inds.length > 0)
          (λ h => elements inds (by simp_all only [decide_eq_true_eq]))

@[reducible]
def s_indicesOf' [DecidableEq α] (xs : List α) (a : α) : CorrectGen (λ (n : Nat) => xs[n]? = some a) :=
  Subtype.mk (indicesOf' xs a) <| by
  funext v
  simp_all
  -- apply List.some_eq_getElem?_iff
  -- apply List.findIdx_getElem?_eq_getElem_of_exists
  sorry

namespace Total

@[simp, aesop safe (rule_sets := [totality])]
theorem total_elements :
    (Gen.total (elements xs h)) := by
  induction xs <;> simp [List.length_pos_iff_exists_cons] at h
  case cons x xs' ih _ =>
    simp [elements]
    cases xs' <;> simp_all

end Total
