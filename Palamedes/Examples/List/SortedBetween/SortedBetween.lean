import Palamedes.Synthesizer

open Gen CorrectGen

@[simp]
def sortedBetweenRec (xs : List Nat) (lo hi : Nat) : Bool :=
  match xs with
  | [] => true
  | x :: xs' => lo <= x && x <= hi && sortedBetweenRec xs' x hi

set_option palamedes.debug true

def genSortedBetween (lo hi : Nat) : Gen (List Nat) := by
  -- generator_search (fun xs => sortedBetweenRec xs lo hi = true)
  let cg : CorrectGen (fun xs => sortedBetweenRec xs lo hi = true) := by
    conv => rhs; apply (List.coerce_to_fold (by rflm) (by intros; simp_all; rflm))
    cgenerator_search
  let g : Gen (List Nat) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g
