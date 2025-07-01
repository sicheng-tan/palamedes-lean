import Palamedes.Synthesizer
import Palamedes.Synthesizer.Util

open Gen CorrectGen

def genLengthKAllTwosFold (k : Nat) : Gen (List Nat) := by
  generator_search (fun xs => List.fold (fun x b => b + 1) 0 xs = k ∧ List.fold (fun x b => x == 2 && b) true xs = true)
