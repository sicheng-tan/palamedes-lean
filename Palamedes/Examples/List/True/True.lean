import Palamedes.Synthesizer

open Gen CorrectGen

namespace ConstTrue

@[simp]
def constTrue : List α → Bool
  | [] => true
  | x :: xs => (fun _ => true) x && constTrue xs

def genTrue : Gen (List Nat) := by
  generator_search (fun xs => constTrue xs = true)

end ConstTrue
