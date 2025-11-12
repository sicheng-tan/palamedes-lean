import Palamedes.Synthesizer

open Gen CorrectGen

namespace TrueAccuOpt

@[simp]
def isTrueAccuOpt (xs : List α) : Option Unit :=
  List.accuM
      (fun _ _ => ())
      (fun x _ _ => guard true)
      (fun _ => some ())
      xs
      ()

/-
(h : ∀ x acc, f x acc = (g x && acc)) :
List.fold f true xs = true ↔
    List.accuM
      (fun _ _ => ())
      (fun x _ _ => guard (g x))
      (fun _ => some ())
      xs
      () = some ()-/

def genTrueAccuOpt : Gen (List Nat) := by
  generator_search (fun xs => isTrueAccuOpt xs = some ())

end TrueAccuOpt
