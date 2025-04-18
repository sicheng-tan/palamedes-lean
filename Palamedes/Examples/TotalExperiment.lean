import Palamedes.Synth
import Palamedes.Sample
import Palamedes.Examples.BST
import Palamedes.Total
import Mathlib.Tactic.Convert

namespace TotalExperiment

-- def genBST' (lo hi : Nat) : Gen (Tree Nat) :=
--   Gen.sized fun n =>
--     unfoldTree n
--       (fun x =>
--         optBind
--           (if h : x.2.fst ≤ x.2.snd then
--             Gen.pick (1, 1) (Gen.ret TreeF.leaf)
--               ((Gen.choose x.2.fst x.2.snd h).bind fun a =>
--                 Gen.guardIn (x.2.fst ≤ a ∧ a ≤ x.2.snd) instDecidableAnd fun _ =>
--                   Gen.ret (TreeF.node () a ()))
--           else Gen.ret TreeF.leaf)
--           fun __do_lift =>
--           match __do_lift with
--           | TreeF.leaf => Gen.ret TreeF.leaf
--           | TreeF.node bl x_1 br =>
--             Gen.ret (TreeF.node (bl, x.snd.fst, x_1 - 1) x_1 (br, x_1 + 1, x.snd.snd)))
--       ((), lo, hi)

-- example {lo hi : Nat} : total (genBST' lo hi) := by
--   intro n
--   induction n generalizing lo hi <;>
--     aesop
--       (add simp total_optBind)
--       (add simp unfoldTree)
--       (add simp pure)
--       (add simp bind)
--       (add simp optBind)
--       (add simp optPick)
--       (add simp total)

end TotalExperiment
