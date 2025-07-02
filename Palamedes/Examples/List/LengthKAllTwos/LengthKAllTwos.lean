import Palamedes.Synthesizer

open Gen CorrectGen

namespace LengthKAllTwos

@[simp]
def allTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && allTwos xs

@[simp]
def lengthK (k : Nat) (xs : List Nat) : Bool :=
  xs.length == k

@[simp]
def lengthKAllTwos (k : Nat) (xs : List Nat) : Bool :=
  xs.length == k && allTwos xs

@[simp]
def genLengthKAllTwos (k : Nat): Gen (List Nat) := by
  generator_search (fun xs => lengthKAllTwos k xs = true)

end LengthKAllTwos
