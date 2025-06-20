import Palamedes.Synthesizer

open Gen CorrectGen

def genLengthKFold {k : Nat} : Gen (List Nat) := by
  generator_search (fun xs => List.fold (fun x b => b + 1) 0 xs = k)
