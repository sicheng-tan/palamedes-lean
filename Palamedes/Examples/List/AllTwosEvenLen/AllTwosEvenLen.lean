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

def genAllTwosEvenLen : Gen (List Nat) := by
  generator_search (fun xs => (recAllTwos xs && recEvenLen xs) = true)
