------------------------------------------------------------
-- Tests for src/Solution.agda
--
-- Every test is a propositional equality proved by `refl`, so the
-- tests "run" at type-checking time:
--
--   agda src/Tests.agda
--
-- A clean exit means every test passed (the equality normalised).
------------------------------------------------------------

module Tests where

open import Solution
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (just; nothing; is-just)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


------------------------------------------------------------
-- Problem 3 — to-nnf  (notes/02-nnf.md)

-- Shorthand from the note: p = x₀, q = x₁, r = x₂
p q r : Formula
p = var 0
q = var 1
r = var 2

-- Worked example from notes/02-nnf.md:
--   φ = ¬f ((p ∨f ¬f q) ∧f r)
--   to-nnf φ  =  (¬p ∧ q) ∨ ¬r
test-nnf-worked :
    to-nnf (¬f ((p ∨f ¬f q) ∧f r))
  ≡ (lit (neg 0) ∧n lit (pos 1)) ∨n lit (neg 2)
test-nnf-worked = refl

-- Smaller sanity checks
test-nnf-var : to-nnf (var 5) ≡ lit (pos 5)
test-nnf-var = refl

test-nnf-double-neg : to-nnf (¬f (¬f var 0)) ≡ lit (pos 0)
test-nnf-double-neg = refl

-- De Morgan: ¬(a ∧ b) ≡ ¬a ∨ ¬b
test-nnf-demorgan-∧ :
    to-nnf (¬f (var 0 ∧f var 1)) ≡ lit (neg 0) ∨n lit (neg 1)
test-nnf-demorgan-∧ = refl

-- De Morgan: ¬(a ∨ b) ≡ ¬a ∧ ¬b
test-nnf-demorgan-∨ :
    to-nnf (¬f (var 0 ∨f var 1)) ≡ lit (neg 0) ∧n lit (neg 1)
test-nnf-demorgan-∨ = refl


------------------------------------------------------------
-- Problem 4 — Assignment  (notes/04-assignments.md)

ρ : Assignment
ρ = (7 , true) ∷ (3 , false) ∷ []

-- Lookup: bound key → just value
test-lookup-head : lookup 7 ρ ≡ just true
test-lookup-head = refl

test-lookup-tail : lookup 3 ρ ≡ just false
test-lookup-tail = refl

-- Lookup: unbound key → nothing
test-lookup-miss : lookup 5 ρ ≡ nothing
test-lookup-miss = refl

-- Insert: updates an existing key in place …
test-insert-update : insert 7 false ρ ≡ (7 , false) ∷ (3 , false) ∷ []
test-insert-update = refl

-- … and appends a fresh key at the end
test-insert-fresh : insert 5 true ρ ≡ (7 , true) ∷ (3 , false) ∷ (5 , true) ∷ []
test-insert-fresh = refl


------------------------------------------------------------
-- Problem 5 — eval on Formula  (notes/04-assignments.md)

σ : Assignment
σ = (0 , true) ∷ (1 , false) ∷ []

-- ¬(x₀ ∧ x₁) under {x₀ ↦ T, x₁ ↦ F}  =  ¬(T ∧ F) = ¬F = T
test-eval-worked : eval σ (¬f (var 0 ∧f var 1)) ≡ just true
test-eval-worked = refl

-- Unbound variable propagates `nothing`
σ′ : Assignment
σ′ = (0 , true) ∷ []

test-eval-nothing : eval σ′ (¬f (var 0 ∧f var 1)) ≡ nothing
test-eval-nothing = refl

-- Strictness: even though false ∧ anything = false, the missing
-- second operand still gives `nothing`.
test-eval-strict : eval σ′ (¬f var 0 ∧f var 1) ≡ nothing
test-eval-strict = refl


------------------------------------------------------------
-- Problem 6 — eval-nnf  (notes/04-assignments.md)

-- ψ = ¬x₀ ∨ x₁, under σ = {x₀ ↦ T, x₁ ↦ F}
--   = ¬T ∨ F = F ∨ F = F
test-eval-nnf-worked :
    eval-nnf σ (lit (neg 0) ∨n lit (pos 1)) ≡ just false
test-eval-nnf-worked = refl

-- eval and eval-nnf agree across to-nnf (spot checks of the
-- correctness statement eval ρ φ ≡ eval-nnf ρ (to-nnf φ))
test-roundtrip-1 :
    eval σ (¬f (var 0 ∧f var 1))
  ≡ eval-nnf σ (to-nnf (¬f (var 0 ∧f var 1)))
test-roundtrip-1 = refl

test-roundtrip-2 :
    eval σ (¬f (¬f var 0 ∨f var 1))
  ≡ eval-nnf σ (to-nnf (¬f (¬f var 0 ∨f var 1)))
test-roundtrip-2 = refl


------------------------------------------------------------
-- Problems 7, 8 — CNF and eval-cnf  (notes/07-cnf.md)

-- χ = (x₀ ∨ ¬x₁) ∧ x₁
χ : CNF
χ = (pos 0 ∨d lit (neg 1)) ∧c dis (lit (pos 1))

-- Under σ = {x₀ ↦ T, x₁ ↦ F}:  (T ∨ T) ∧ F  =  F
test-eval-cnf-false : eval-cnf σ χ ≡ just false
test-eval-cnf-false = refl

-- χ′ = (x₀ ∨ x₁) ∧ ¬x₁,  under σ:  (T ∨ F) ∧ T  =  T
test-eval-cnf-true :
    eval-cnf σ ((pos 0 ∨d lit (pos 1)) ∧c dis (lit (neg 1))) ≡ just true
test-eval-cnf-true = refl

-- Unbound variable propagates `nothing`  (σ′ binds only x₀)
test-eval-cnf-nothing : eval-cnf σ′ χ ≡ nothing
test-eval-cnf-nothing = refl


------------------------------------------------------------
-- Problem 9 — sat?  (notes/09-sat.md)
--
-- `sat? φ` returns `sat ρ p` with p : eval-cnf ρ φ ≡ just true, so a
-- found model is correct *by type* — we only need to test that the
-- solver answers sat/unsat on the right formulas.

is-sat : {φ : CNF} → SatResult φ → Bool
is-sat (sat _ _) = true
is-sat unsat     = false

-- (x₀ ∨ x₁) ∧ ¬x₀  is satisfiable (x₀ = F, x₁ = T)
test-sat-sat : is-sat (sat? ((pos 0 ∨d lit (pos 1)) ∧c dis (lit (neg 0)))) ≡ true
test-sat-sat = refl

-- x₀ ∧ ¬x₀  is unsatisfiable
test-sat-unsat : is-sat (sat? (lit (pos 0) ∧c dis (lit (neg 0)))) ≡ false
test-sat-unsat = refl

-- The solver finds the concrete model {x₀ ↦ F, x₁ ↦ T}, and the
-- accompanying proof obligation eval-cnf ρ φ ≡ just true is `refl`.
test-sat-model :
    sat? ((pos 0 ∨d lit (pos 1)) ∧c dis (lit (neg 0)))
  ≡ sat ((0 , false) ∷ (1 , true) ∷ []) refl
test-sat-model = refl


------------------------------------------------------------
-- Problem 11 — to-cnf (Tseytin)  (notes/11-tseytin.md)

-- A lone literal needs no fresh variables
test-tseytin-lit : to-cnf (lit (pos 0)) ≡ dis (lit (pos 0))
test-tseytin-lit = refl

-- Exact clause shape for one ∧-node (x₀ ∧ x₁, fresh variable x₂):
--   x₂ ∧ (¬x₂ ∨ x₀) ∧ (¬x₂ ∨ x₁) ∧ (¬x₀ ∨ ¬x₁ ∨ x₂)
-- (the worked example in notes/11-tseytin.md §6)
test-tseytin-and :
    to-cnf (lit (pos 0) ∧n lit (pos 1))
  ≡ (lit (pos 2)) ∧c (neg 2 ∨d lit (pos 0))
                  ∧c (neg 2 ∨d lit (pos 1))
                  ∧c dis (neg 0 ∨d (neg 1 ∨d lit (pos 2)))
test-tseytin-and = refl

-- Exact clause shape for one ∨-node (x₀ ∨ x₁, fresh variable x₂):
--   x₂ ∧ (¬x₂ ∨ x₀ ∨ x₁) ∧ (¬x₀ ∨ x₂) ∧ (¬x₁ ∨ x₂)
test-tseytin-or :
    to-cnf (lit (pos 0) ∨n lit (pos 1))
  ≡ (lit (pos 2)) ∧c (neg 2 ∨d (pos 0 ∨d lit (pos 1)))
                  ∧c (neg 0 ∨d lit (pos 2))
                  ∧c dis (neg 1 ∨d lit (pos 2))
test-tseytin-or = refl

-- Equisatisfiability spot checks: sat? agrees on ψ and to-cnf ψ.
-- x₀ ∧ ¬x₀ (unsat NNF) stays unsat after Tseytin …
test-tseytin-unsat :
    is-sat (sat? (to-cnf (lit (pos 0) ∧n lit (neg 0)))) ≡ false
test-tseytin-unsat = refl

-- … and (¬x₀ ∨ x₁) ∧ x₀ (sat NNF, e.g. x₀ = x₁ = T) stays sat
test-tseytin-sat :
    is-sat (sat? (to-cnf ((lit (neg 0) ∨n lit (pos 1)) ∧n lit (pos 0)))) ≡ true
test-tseytin-sat = refl


------------------------------------------------------------
-- Problem 12 — sat-formula? and solve  (notes/12-formula-sat.md)
--
-- As with sat?, a `sat ρ p` answer carries p : eval ρ φ ≡ just true,
-- so models are correct by construction.

has-solution : Formula → Bool
has-solution φ = is-just (solve φ)

-- ¬(x₀ ∧ ¬x₀) is a tautology, hence satisfiable
test-solve-tautology : has-solution (¬f (var 0 ∧f ¬f var 0)) ≡ true
test-solve-tautology = refl

-- x₀ ∧ ¬x₀ is unsatisfiable
test-solve-contradiction : has-solution (var 0 ∧f ¬f var 0) ≡ false
test-solve-contradiction = refl

-- End-to-end pipeline on a compound formula: (x₀ ∨ x₁) ∧ ¬x₀
test-solve-pipeline : has-solution ((var 0 ∨f var 1) ∧f ¬f var 0) ≡ true
test-solve-pipeline = refl

-- The concrete model for the simplest formula
test-solve-model : solve (var 0) ≡ just ((0 , true) ∷ [])
test-solve-model = refl
