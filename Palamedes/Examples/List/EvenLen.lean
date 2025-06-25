import Palamedes.Synthesizer

open Gen CorrectGen

def genEvenLenFold : Gen (List Nat) := by
  generator_search (fun xs => List.fold (fun x b => !b) true xs = true)

@[simp]
def recEvenLen : List α → Bool
  | [] => true
  | _ :: xs => !(recEvenLen xs)

set_option palamedes.debug true

-- def genEvenLenRec : Gen (List Nat) := by
--   -- generator_search (fun xs => recEvenLen xs = true)
--   let cg : CorrectGen (fun xs => recEvenLen xs = true) := by
--     apply convert (by
--       funext
--       simp [guard, *]
--       conv => rhs; lhs; apply (List.coerce_to_fold (by rflm) (by intros; simp_all; rflm))
--       ) (List.s_unfold _)
--   let g : Gen (List Nat) := by
--     optimize_gen cg.val
--   let _ : support cg.val = support g := by
--     optimality
--   let _ : Gen.total g := by
--     totality
--   exact g

-- def genEvenLen : Gen (List Nat) := by
--   generator_search (fun xs => Nat.mod (List.length xs) 2 == 0)
