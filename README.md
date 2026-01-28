# Palamedes

NOTE: The code for this project is still under construction. The core pieces work well, but there
are rough edges all over the place. We plan to clean up the code this Spring when we have more time,
but for the moment you should consider all APIs unstable.

We will read issues that are posted, but we make no promises about how quickly those issues will be
addressed.

## Files
1. Gen.lean contains the basic generator type and a function to compute the _support_ of a
   generator, plus a couple of useful theorems about the supports of different structures (map,
   dependent conditionals, etc.).
2. CorrectGen.lean refines the generator type with a predicate and defines basic synthesis rules
3. Synthesizer/CGeneratorSearch.lean adds all the synthesis rules to aesop (see the AesopRules
   section), adds some macros for goal manipulation and for controlling when certain rules apply,
   and defines the API (see API).
4. The Data folder contains several recursive datatypes, along with synthesis rules for them (using
   the unfold strategy described in the paper), useful lemmas for manipulating predicates about them
   into the right forms, and lemmas about support and termination. It also contains base types like
   Nat along with synthesis rules for them, in some cases rules for casing on them, and lemmas about
   supports and totality.
5. The Examples folder contains examples, both simple ones (Simple.lean and
   Range.lean) and complex ones using the recursive datatypes.