import Palamedes.Synthesizer

open Gen CorrectGen

namespace AllEvensAccuOpt

@[simp]
def isAllEvensAccuOpt (xs : List Nat) : Option Unit :=
  List.accuM (fun _ _ => ()) (fun x _ _ => guard (x % 2 == 0)) (fun _ => some ()) xs ()

def genAllEvensAccuOpt : Gen (List Nat) := by
  generator_search (fun xs => isAllEvensAccuOpt xs = some ())


theorem foo : ∃ g : Nat → Bool,
  f = (fun x b => x % 2 == 0 && b) →
  -- (h : ∀ x acc, f x acc = (g x && acc)) →
  (List.fold f true xs = true ↔
  List.accuM
    (fun _ _ => ())
    (fun x _ _ => guard (g x))
    (fun _ => some ())
    xs
    () = some () ) := by
  refine Exists.intro ?g ?p
  case p =>
    intros hf
    apply List.fold_accu_Option_true
    aesop

#print foo

end AllEvensAccuOpt
