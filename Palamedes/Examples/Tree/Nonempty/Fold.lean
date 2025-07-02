import Palamedes.Synthesizer

open Gen CorrectGen

namespace NonemptyFold

def nonemptyFold (t : Tree Nat) : Bool :=
  Tree.fold (fun _ _ _ => true) false t

def genNonemptyFold : Gen (Tree Nat) := by
  generator_search (fun t => nonemptyFold t = true)

end NonemptyFold
