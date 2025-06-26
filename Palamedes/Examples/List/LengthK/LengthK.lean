import Palamedes.Synthesizer

open Gen CorrectGen

def genLengthK {k : Nat} : Gen (List Nat) := by
  generator_search (fun xs => List.length xs = k)
