import Palamedes.Synthesizer

open Gen CorrectGen

set_option palamedes.debug true

def genLengthKAllTwosFold (k : Nat) : Gen (List Nat) := by
  -- generator_search (fun xs => List.fold (fun x b => b + 1) 0 xs = k ∧ List.fold (fun x b => x == 2 && b) true xs = true)
  let cg : CorrectGen (fun xs => List.fold (fun x b => b + 1) 0 xs = k ∧ List.fold (fun x b => x == 2 && b) true xs = true) := by
    apply convert (by norm_for_List_unfold) (List.s_unfold _)
    (repeat apply duncurry); intro
    (repeat apply duncurry); intro
    (repeat apply duncurry); intro
    (repeat apply duncurry); intro
    rename_i n _ _ _
    apply s_caseNat n (by intros; rflm)
    . cgenerator_search
    . (repeat apply duncurry); intro
      apply convert (by
        funext
        /- PROBLEM: the and_assoc is the issue
           (adding it in simp_predicate breaks other things) -/
        try simp [guard, Option.bind_eq_some_iff, and_assoc, *]
        first
          | rfl
          | apply exists_congr; intro; rw [true_and]
        ) (s_bind _ _)
      . cgenerator_search
      . cgenerator_search
  let g : Gen (List Nat) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g
