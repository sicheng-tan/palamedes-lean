import Palamedes.Synthesizer

open Gen CorrectGen

def genAllTwosFold : Gen (List Nat) := by
  generator_search (fun xs => List.fold (fun x b => x == 2 && b) true xs = true)

@[simp]
def recAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && recAllTwos xs

def genAllTwosRec : Gen (List Nat) := by
  generator_search (fun xs => recAllTwos xs)

-- def genAllTwos : Gen (List Nat) := by
--   generator_search (fun xs => List.all xs ( · = 2))
