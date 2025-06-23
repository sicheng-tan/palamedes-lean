import Palamedes.Synthesizer

open Gen CorrectGen

def genAllTwosFold : Gen (List Nat) := by
  generator_search (fun xs => List.fold (fun x b => x == 2 && b) true xs = true)

set_option palamedes.debug true

-- def genAllTwos : Gen (List Nat) := by
--   generator_search (fun xs => List.all xs ( · = 2))
