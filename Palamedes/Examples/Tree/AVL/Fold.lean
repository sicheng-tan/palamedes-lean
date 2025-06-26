import Palamedes.Synthesizer
import Palamedes.Examples.Tree.BST.BST

open Gen CorrectGen

-- def genAVL (height lo hi : Nat) : Gen (Tree Nat) := by
--    generator_search ( fun t =>
--     Tree.fold
--       (fun bl x br h => h > 0 && bl (h - 1) && br (h - 1))
--       (fun h => h <= 1)
--       t
--       height
--     ∧
--     Tree.fold
--       (fun bl x br bounds =>
--         match bounds with
--         | (sl, sr) => (decide (sl ≤ x) && decide (x ≤ sr)) && bl (sl, x - 1) && br (x + 1, sr))
--       (fun _ => true)
--       t
--       (lo, hi) = true
--     )
