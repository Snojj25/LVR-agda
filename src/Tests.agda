-- Tests for src/Solution.agda. Everything is a propositional equality
-- proved by refl, so the tests "run" during type-checking:
-- if `agda src/Tests.agda` goes through, all tests pass.

module Tests where

open import Solution
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (just; nothing; is-just)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


-- Problem 3: to-nnf

p q r : Formula
p = var 0
q = var 1
r = var 2

-- worked example from the notes: ¬((p ∨ ¬q) ∧ r)  ~>  (¬p ∧ q) ∨ ¬r
test-nnf-worked :
    to-nnf (¬f ((p ∨f ¬f q) ∧f r))
  ≡ (lit (neg 0) ∧n lit (pos 1)) ∨n lit (neg 2)
test-nnf-worked = refl

test-nnf-var : to-nnf (var 5) ≡ lit (pos 5)
test-nnf-var = refl

test-nnf-double-neg : to-nnf (¬f (¬f var 0)) ≡ lit (pos 0)
test-nnf-double-neg = refl

-- both De Morgan directions
test-nnf-demorgan-∧ :
    to-nnf (¬f (var 0 ∧f var 1)) ≡ lit (neg 0) ∨n lit (neg 1)
test-nnf-demorgan-∧ = refl

test-nnf-demorgan-∨ :
    to-nnf (¬f (var 0 ∨f var 1)) ≡ lit (neg 0) ∧n lit (neg 1)
test-nnf-demorgan-∨ = refl


-- Problem 4: lookup / insert

ρ : Assignment
ρ = (7 , true) ∷ (3 , false) ∷ []

test-lookup-head : lookup 7 ρ ≡ just true
test-lookup-head = refl

test-lookup-tail : lookup 3 ρ ≡ just false
test-lookup-tail = refl

test-lookup-miss : lookup 5 ρ ≡ nothing
test-lookup-miss = refl

-- insert updates an existing key in place
test-insert-update : insert 7 false ρ ≡ (7 , false) ∷ (3 , false) ∷ []
test-insert-update = refl

-- and appends a fresh one at the end
test-insert-fresh : insert 5 true ρ ≡ (7 , true) ∷ (3 , false) ∷ (5 , true) ∷ []
test-insert-fresh = refl


-- Problem 5: eval

σ : Assignment
σ = (0 , true) ∷ (1 , false) ∷ []

-- ¬(x₀ ∧ x₁) under {x₀=T, x₁=F} is true
test-eval-worked : eval σ (¬f (var 0 ∧f var 1)) ≡ just true
test-eval-worked = refl

-- unbound variable gives nothing
σ′ : Assignment
σ′ = (0 , true) ∷ []

test-eval-nothing : eval σ′ (¬f (var 0 ∧f var 1)) ≡ nothing
test-eval-nothing = refl

-- eval is strict: false ∧ undefined is still nothing, not just false
test-eval-strict : eval σ′ (¬f var 0 ∧f var 1) ≡ nothing
test-eval-strict = refl


-- Problem 6: eval-nnf

test-eval-nnf-worked :
    eval-nnf σ (lit (neg 0) ∨n lit (pos 1)) ≡ just false
test-eval-nnf-worked = refl

-- spot checks that eval and eval-nnf agree across to-nnf
test-roundtrip-1 :
    eval σ (¬f (var 0 ∧f var 1))
  ≡ eval-nnf σ (to-nnf (¬f (var 0 ∧f var 1)))
test-roundtrip-1 = refl

test-roundtrip-2 :
    eval σ (¬f (¬f var 0 ∨f var 1))
  ≡ eval-nnf σ (to-nnf (¬f (¬f var 0 ∨f var 1)))
test-roundtrip-2 = refl


-- Problems 7, 8: CNF in eval-cnf

-- χ = (x₀ ∨ ¬x₁) ∧ x₁
χ : CNF
χ = (pos 0 ∨d lit (neg 1)) ∧c dis (lit (pos 1))

test-eval-cnf-false : eval-cnf σ χ ≡ just false
test-eval-cnf-false = refl

test-eval-cnf-true :
    eval-cnf σ ((pos 0 ∨d lit (pos 1)) ∧c dis (lit (neg 1))) ≡ just true
test-eval-cnf-true = refl

test-eval-cnf-nothing : eval-cnf σ′ χ ≡ nothing
test-eval-cnf-nothing = refl


-- Problem 9: sat?
--
-- A found model is correct by type (sat carries the proof), so here we
-- mostly just check that the solver says sat/unsat on the right formulas.

is-sat : {φ : CNF} → SatResult φ → Bool
is-sat (sat _ _) = true
is-sat unsat     = false

-- (x₀ ∨ x₁) ∧ ¬x₀ is satisfiable
test-sat-sat : is-sat (sat? ((pos 0 ∨d lit (pos 1)) ∧c dis (lit (neg 0)))) ≡ true
test-sat-sat = refl

-- x₀ ∧ ¬x₀ is not
test-sat-unsat : is-sat (sat? (lit (pos 0) ∧c dis (lit (neg 0)))) ≡ false
test-sat-unsat = refl

-- the concrete model it finds, with the proof obligation closed by refl
test-sat-model :
    sat? ((pos 0 ∨d lit (pos 1)) ∧c dis (lit (neg 0)))
  ≡ sat ((0 , false) ∷ (1 , true) ∷ []) refl
test-sat-model = refl


-- Problem 11: to-cnf (Tseytin)

-- a lone literal needs no fresh variables
test-tseytin-lit : to-cnf (lit (pos 0)) ≡ dis (lit (pos 0))
test-tseytin-lit = refl

-- exact clause shape for one ∧-node (x₀ ∧ x₁, fresh variable x₂):
--   x₂ ∧ (¬x₂ ∨ x₀) ∧ (¬x₂ ∨ x₁) ∧ (¬x₀ ∨ ¬x₁ ∨ x₂)
test-tseytin-and :
    to-cnf (lit (pos 0) ∧n lit (pos 1))
  ≡ (lit (pos 2)) ∧c (neg 2 ∨d lit (pos 0))
                  ∧c (neg 2 ∨d lit (pos 1))
                  ∧c dis (neg 0 ∨d (neg 1 ∨d lit (pos 2)))
test-tseytin-and = refl

-- and for one ∨-node:
--   x₂ ∧ (¬x₂ ∨ x₀ ∨ x₁) ∧ (¬x₀ ∨ x₂) ∧ (¬x₁ ∨ x₂)
test-tseytin-or :
    to-cnf (lit (pos 0) ∨n lit (pos 1))
  ≡ (lit (pos 2)) ∧c (neg 2 ∨d (pos 0 ∨d lit (pos 1)))
                  ∧c (neg 0 ∨d lit (pos 2))
                  ∧c dis (neg 1 ∨d lit (pos 2))
test-tseytin-or = refl

-- equisatisfiability spot checks: sat? agrees on ψ and to-cnf ψ
test-tseytin-unsat :
    is-sat (sat? (to-cnf (lit (pos 0) ∧n lit (neg 0)))) ≡ false
test-tseytin-unsat = refl

test-tseytin-sat :
    is-sat (sat? (to-cnf ((lit (neg 0) ∨n lit (pos 1)) ∧n lit (pos 0)))) ≡ true
test-tseytin-sat = refl


-- Problem 12: sat-formula? in solve

has-solution : Formula → Bool
has-solution φ = is-just (solve φ)

-- ¬(x₀ ∧ ¬x₀) is a tautology
test-solve-tautology : has-solution (¬f (var 0 ∧f ¬f var 0)) ≡ true
test-solve-tautology = refl

test-solve-contradiction : has-solution (var 0 ∧f ¬f var 0) ≡ false
test-solve-contradiction = refl

-- end-to-end pipeline on a compound formula
test-solve-pipeline : has-solution ((var 0 ∨f var 1) ∧f ¬f var 0) ≡ true
test-solve-pipeline = refl

test-solve-model : solve (var 0) ≡ just ((0 , true) ∷ [])
test-solve-model = refl
