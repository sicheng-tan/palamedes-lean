import Palamedes.Synthesizer

open Gen CorrectGen

namespace Nonempty

@[simp]
def nonempty : Tree α → Bool
  | .leaf => false
  | .node l _ r => true && nonempty l && nonempty r

def genNonempty : Gen (Tree Nat) := by
  generator_search (fun t => nonempty t = true)

end Nonempty
