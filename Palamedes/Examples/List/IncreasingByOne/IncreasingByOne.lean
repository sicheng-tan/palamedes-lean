import Palamedes.Synthesizer

open Gen CorrectGen

namespace IncreasingByOneList

@[simp]
def increasingByOneAux (xs : List Nat) (prev : Nat) : Bool :=
  match xs with
  | [] => true
  | x :: xs' => x == prev + 1 && increasingByOneAux xs' x

@[simp]
def increasingByOne (xs : List Nat) : Bool :=
  increasingByOneAux xs 0

def genIncreasingByOneRec : Gen (List Nat) := by
  generator_search (fun xs => increasingByOne xs = true)

end IncreasingByOneList
