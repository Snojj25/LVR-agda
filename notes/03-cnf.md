# Note 03 — Conjunctive Normal Form (Problems 7 & 8)

Problems 7 and 8: the CNF type and its evaluator. Code:
`src/Solution.agda` lines 200–226.

## 1. What is CNF?

A formula is in **conjunctive normal form** if it is a *conjunction*
of *disjunctions* of *literals*:

```
(ℓ₁₁ ∨ ⋯ ∨ ℓ₁ₖ₁) ∧ (ℓ₂₁ ∨ ⋯ ∨ ℓ₂ₖ₂) ∧ ⋯ ∧ (ℓₘ₁ ∨ ⋯ ∨ ℓₘₖₘ)
```

| level  | what it is                          | our Agda type |
| ------ | ----------------------------------- | ------------- |
| top    | conjunction of clauses              | `CNF`         |
| middle | clause: disjunction of literals     | `Disjunct`    |
| atom   | literal: variable or its negation   | `Literal`     |

No nesting beyond this: no `∧` inside a clause, no `∨` between
clauses. This rigidity makes CNF easy to manipulate algorithmically.

## 2. Why CNF matters

CNF is the *lingua franca* of practical SAT solving. Every modern
solver (MiniSat, CaDiCaL, Glucose, …) accepts CNF input and is built
around clause-level reasoning (unit propagation, watched literals,
clause learning). To use a SAT solver, you first translate to CNF —
which is what Problem 7 sets up and Problem 9 (note 05) consumes.

## 3. The grammar typo

The handout prints `CNF → Disjunct ∨ CNF`, which is wrong twice: the
top connective of a *conjunctive* NF must be `∧`, and there is no
base case. We fix it to

```
CNF → Disjunct  |  Disjunct ∧ CNF
```

— a non-empty conjunction of disjuncts.

## 4. The Agda definition

```agda
data Disjunct : Set where
  lit  : Literal → Disjunct
  _∨d_ : Literal → Disjunct → Disjunct

data CNF : Set where
  dis  : Disjunct → CNF
  _∧c_ : Disjunct → CNF → CNF

infixr 6 _∨d_
infixr 7 _∧c_
```

Each constructor mirrors one grammar production.

### Why non-empty (not `List`)?

Both types are essentially non-empty lists:

```
Disjunct ≅ List⁺ Literal       CNF ≅ List⁺ Disjunct
```

We rule out the degenerate cases at the type level:

- An empty disjunction is `false` — would make every CNF containing it
  unsatisfiable.
- An empty conjunction is `true` — vacuously satisfied.

Forcing non-emptiness means recursion in `eval-disjunct` and
`eval-cnf` always has something to look at, with no special cases.
(Real solvers do use the empty clause as the **UNSAT signal** at
runtime, but that's an algorithmic concern, not a syntactic one.)

## 5. From any formula to CNF

**Theorem.** Every formula `φ` is equivalent to some CNF `φ'`.

**Sketch.** Two phases:

1. Convert `φ` to NNF (note 02).
2. Distribute: apply

   ```
   a ∨ (b ∧ c) ≡ (a ∨ b) ∧ (a ∨ c)
   (a ∧ b) ∨ c ≡ (a ∨ c) ∧ (b ∨ c)
   ```

   until every `∨` is below every `∧`.

The result is correct but can blow up exponentially. For
`(a₁ ∧ b₁) ∨ ⋯ ∨ (aₙ ∧ bₙ)` (size `2n`), distribution produces `2ⁿ`
clauses. That motivates the **Tseytin transformation** (note 06): an
*equisatisfiable* CNF of linear size, with fresh variables for
internal nodes.

We don't implement either conversion here — Problem 7 takes CNF as
given and Problem 9 writes a solver for it.

## 6. Evaluation (Problem 8)

```agda
eval-disjunct : Assignment → Disjunct → Maybe Bool
eval-disjunct ρ (lit ℓ)   = eval-lit ρ ℓ
eval-disjunct ρ (ℓ ∨d d)  with eval-lit ρ ℓ | eval-disjunct ρ d
... | just x | just y = just (x or y)
... | _      | _      = nothing

eval-cnf : Assignment → CNF → Maybe Bool
eval-cnf ρ (dis d)   = eval-disjunct ρ d
eval-cnf ρ (d ∧c φ)  with eval-disjunct ρ d | eval-cnf ρ φ
... | just x | just y = just (x and y)
... | _      | _      = nothing
```

Return type `Maybe Bool`: same partial-evaluation convention as `eval`
(note 04). `nothing` propagates outward: this is **strict**, not
short-circuit. If `ρ` doesn't bind every variable in the formula,
expect `nothing` — even if logically the clause is already decided
by the bindings present. The SAT solver only calls `eval-cnf` on
total assignments, so `nothing` never occurs there.

### Quick example

```agda
ρ = (0 , true) ∷ (1 , false) ∷ (2 , true) ∷ []
φ = (pos 0 ∨d lit (neg 1)) ∧c dis (neg 0 ∨d lit (pos 2))
```

First clause: `eval-lit (pos 0) = just true` and `eval-lit (neg 1) =
just true`, so `just (true or true) = just true`. Second clause
similarly `just true`. Conjunction: `just true`.

Drop variable 2: the second clause becomes `nothing`, so `eval-cnf`
returns `nothing` overall.
