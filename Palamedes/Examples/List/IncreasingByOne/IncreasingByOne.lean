import Palamedes.Synthesizer

open Gen CorrectGen

@[simp]
def increasingByOneRecAux (xs : List Nat) (prev : Nat) : Bool :=
  match xs with
  | [] => true
  | x :: xs' => x == prev + 1 && increasingByOneRecAux xs' x

@[simp]
def increasingByOneRec (xs : List Nat) : Bool :=
  increasingByOneRecAux xs 0

def genIncreasingByOneRec : Gen (List Nat) := by
  generator_search (fun xs => increasingByOneRec xs = true)
