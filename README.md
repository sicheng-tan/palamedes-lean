# palamedes

Files:
* `Decidable.lean`: rewriting lemmas for terms with `if`
* `RuleSets.lean`: hint databases for aesop
    * [deps: `Aesop`]
* `RawGen.lean`: the generator type
* `Gen.lean`: smart constructors for generators
    * [deps: `Palamedes.RawGen`]
* `Sample.lean`: infrastructure for sampling from a generator
    * [deps: `Palamedes.Gen`, `Plausible.Random`]
* `Support.lean`: TODO
    * [deps: `Aesop`, `Palamedes.Gen`]
* `Data`: lemmas for building generators for common recursive data structures
    * `List.lean`
        * [deps: `Palamedes.Support`]
    * `Tree.lean`
        * [deps: `Palamedes.Support`]
* `InternalizeProofs.lean`: converts a proof that a generator's outputs satisfy a predicate into a generator of values with accompanying proofs that they satisfy the predicate
    * [deps: `Palamedes.Support`]
* `Synth.lean`: generator synthesis rules and tactics
    * [deps: `Palamedes.Support`, `Palamedes.Data.List`, `Palamedes.Data.Tree`, `Palamedes.Decidable`, `Palamedes.RuleSets`, `Palamedes.InternalizeProofs`]
* `Total.lean`: predicate and theorems for backtracking-free generators
    * [deps: `Palamedes.Support`]
* `Basic.lean`: simple examples
    * [deps: `Palamedes.Synth`, `Palamedes.Sample`, `Palamedes.Data.Tree`, `Mathlib.Tactic.Convert`]
* `Examples`: extended examples
    * `BST.lean`
        * [deps: `Palamedes.Synth`, `Palamedes.Sample`, `Palamedes.Data.Tree`, `Mathlib.Tactic.Convert`]
    * `Inductive.lean`
        * [deps: `Palamedes.Synth`]
    * `STLC.lean`
        * [deps: `Palamedes.Synth`, `Palamedes.Sample`]
* `Experiments`: in-progress ideas
    * `Gen2.lean`
        * [deps: `Aesop`]
    * `List2.lean`
        * [deps: `Palamedes.Support`, `Mathlib.Logic.Equiv.Basic`]
    * `Recursion.lean`
        * [deps: `Palamedes.Synth`, `Palamedes.Sample`, `Palamedes.Data.Tree`, `Mathlib.Tactic.Convert`]
    * `TotalExperiment.lean`
        * [deps: `import Palamedes.Synth`, `Palamedes.Sample`, `Palamedes.Examples.BST`, `Palamedes.Total`, `Mathlib.Tactic.Convert`]
* `Render.lean`: simplification of synthesized generators
    * [deps: `Palamedes.Synth`, `Palamedes.Sample`, `Palamedes.Examples.BST`, `Mathlib.Tactic.Convert`]