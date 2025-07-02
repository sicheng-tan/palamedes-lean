import Palamedes.Synthesizer

open Gen CorrectGen

namespace IncreasingByOneListFold

def increasingByOneFold (xs : List Nat) : Bool :=
  List.fold (fun x b prev => x == prev + 1 && b x) (fun _ => true) xs 0

def genIncreasingByOneFold : Gen (List Nat) := by
  generator_search (fun xs => increasingByOneFold xs = true)

end IncreasingByOneListFold
