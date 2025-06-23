import Palamedes.Synthesizer

open Gen CorrectGen

def elements (xs : List α) (h : xs.length > 0) : Gen α :=
  match xs with
  | x :: xs =>
    match hxs : xs with
    | [] => pure x
    | _ :: _ => pick (pure x) (elements xs (by rw [hxs]; simp))

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

def s_elements_partial [DecidableEq α] (xs : List α) : CorrectGen (λ v => List.elem v xs) :=
  Subtype.mk (assume (xs.length > 0) (λ h => elements xs (by aesop))) <| by
    funext v
    simp [support_elements]
    cases xs <;> simp_all
