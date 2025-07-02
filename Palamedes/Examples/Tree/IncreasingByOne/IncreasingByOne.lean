import Palamedes.Synthesizer

open Gen CorrectGen

namespace IncreasingByOneTree

@[simp]
def increasingByOneAux (t : Tree Nat) (prev : Nat) : Bool :=
  match t with
  | .leaf => true
  | .node l x r => x == prev + 1 && increasingByOneAux l x && increasingByOneAux r x

@[simp]
def increasingByOne (t : Tree Nat) : Bool :=
  increasingByOneAux t 0

def genIncreasingByOne : Gen (Tree Nat) := by
  generator_search (fun t => increasingByOne t = true)

end IncreasingByOneTree
