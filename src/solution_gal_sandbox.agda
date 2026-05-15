------------------------------------------------------------
-- solution_gal_sandbox.agda  —  personal step-by-step lab
--
-- Agda does not allow hyphens in module names, so the file is
-- solution_gal_sandbox.agda  (underscores).  Check it with:
--
--   cd …/LVR-agda && agda src/solution_gal_sandbox.agda
--
-- Right now this file is *intentionally incomplete* for Problem 1:
-- it will NOT type-check until you follow the steps below.
------------------------------------------------------------

module solution_gal_sandbox where

open import Data.Nat using (ℕ)


------------------------------------------------------------
-- Problem 1 — Formula  (INCOMPLETE ON PURPOSE)
------------------------------------------------------------
--
-- Target grammar (from the project handout):
--
--   Formula → Var n
--           | ¬ Formula
--           | Formula ∧ Formula
--           | Formula ∨ Formula
--
-- STEPS (do in order; run `agda src/solution_gal_sandbox.agda` after each):
--
--   1. Add the missing constructors below (only `var` is there now).
--   2. Uncomment the examples in section “Examples (broken until step 1)”.
--   3. Copy `infix` declarations from `Solution.agda` Problem 1 so that
--      `a ∧f b` parses with sensible precedence.
--   4. (Optional) open `Data.Bool` and rename `_∧_` / `_∨_` like in
--      `Solution.agda` if you later add evaluation here.
------------------------------------------------------------

data Formula : Set where
  var : ℕ → Formula
  -- STEP 1a:  ¬f_  : Formula → Formula
  -- STEP 1b:  _∧f_ : Formula → Formula → Formula
  -- STEP 1c:  _∨f_ : Formula → Formula → Formula


------------------------------------------------------------
-- Examples (broken until you finish STEP 1)
------------------------------------------------------------
--
-- Uncomment these lines *after* the datatype is complete.
-- Until then, Agda will complain about unknown identifiers.
--

-- broken-1 : Formula
-- broken-1 = var 0 ∧f var 1

-- broken-2 : Formula
-- broken-2 = ¬f (var 0 ∨f var 1)

-- THIS line is active on purpose — it references constructors
-- you have not written yet, so the file fails to check:
oops : Formula
oops = var 0 ∧f var 1
