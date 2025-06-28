import Palamedes.Synthesizer

open Gen CorrectGen

namespace AllTwosEvenLen

@[simp]
def recAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && recAllTwos xs

@[simp]
def recEvenLen : List α → Bool
  | [] => true
  | _ :: xs => !(recEvenLen xs)

set_option palamedes.debug true

def genAllTwosEvenLen : Gen (List Nat) := by
  -- generator_search (fun xs => (recAllTwos xs && recEvenLen xs) = true)
  let cg : CorrectGen (fun (xs: List Nat) => (recAllTwos xs && recEvenLen xs) = true) := by
    -- NOTE: this is exactly the same as the fold version
    apply convert (by
      funext
      simp [guard, *]
      rw [← List.merge_accuM]
      all_goals sorry
      -- apply and_congr
      -- . simp_list_predicate
      -- . simp_list_predicate
    ) (List.s_unfold _)
    sorry
    -- intros s b
    -- replace ⟨s1, s2⟩ := s
    -- apply caseBool s2
    -- . intro
    --   gapply (s_pick _ _)
    --   . cgenerator_search
    --   . apply convert (by
    --       funext
    --       simp [guard, *, Option.bind_eq_some_iff]
    --       apply exists_congr; intro; rw [true_and]) (s_bind _ _)
    --     . cgenerator_search
    --     . cgenerator_search
    -- . intro
    --   apply convert (by
    --     funext
    --     simp [guard, *]
    --     rw [exists_comm]
    --     apply exists_congr; intro; rw [true_and]
    --   ) (s_bind _ _)
    --   . cgenerator_search
    --   . intro
    --     apply convert (by
    --       funext
    --       simp [guard, *, Option.bind_eq_some_iff]
    --       rfl) (s_pure _)
  let g : Gen (List Nat) := by
    optimize_gen cg.val
  exact g
