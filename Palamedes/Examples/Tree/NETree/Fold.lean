import Palamedes.Synthesizer

open Gen CorrectGen

def genNETreeFold : Gen (Tree Nat) := by
  generator_search (fun t => Tree.fold (fun _ _ _ => true) false t)
