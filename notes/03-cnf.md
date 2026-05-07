# Note 03 — Conjunctive Normal Form (Problems 7 & 8)

This note covers Problems 7 and 8: the Agda type of CNF formulas and how
to evaluate them under a (possibly partial) assignment. Code lives in
[`src/Solution.agda`](../src/Solution.agda) — Problem 7 (lines 180–202)
and Problem 8 (lines 205–219).

Prerequisites:

- Note 02 (NNF). We reuse `Literal` and `eval-lit`, and the
  "every formula has a CNF" argument starts by going through NNF.
- Note 05 (SAT). CNF is what feeds the DPLL solver in Problem 9.
- Note 06 (Tseytin). The naive CNF construction can blow up
  exponentially; Tseytin's transformation is the polynomial-size fix.


## 1. What is conjunctive normal form?

A formula is in **conjunctive normal form** (CNF) if it is a
*conjunction* of *disjunctions* of *literals*:

```
(ℓ₁₁ ∨ ℓ₁₂ ∨ … ∨ ℓ₁ₖ₁) ∧ (ℓ₂₁ ∨ ℓ₂₂ ∨ … ∨ ℓ₂ₖ₂) ∧ … ∧ (ℓₘ₁ ∨ … ∨ ℓₘₖₘ)
```

Each `ℓᵢⱼ` is a literal (a variable `xₙ` or its negation `¬xₙ`, exactly
the `Literal` type from Note 02). Each parenthesised group is a
**clause** (in our Agda spelling, a `Disjunct`).

The layered vocabulary, outside in:

| level  | what it is                            | our Agda type |
| ------ | ------------------------------------- | ------------- |
| top    | a conjunction of clauses              | `CNF`         |
| middle | a clause: a disjunction of literals   | `Disjunct`    |
| atom   | a literal: a variable or its negation | `Literal`     |

Every level is a flat list of the level below joined by a single fixed
connective (`∧` between clauses, `∨` inside a clause). No nesting beyond
that: no `∧` inside a clause, no `∨` between clauses. That rigidity is
what makes CNF easy to manipulate algorithmically.


## 2. Why CNF matters

CNF is the *lingua franca* of practical SAT solving. Every modern
industrial solver — MiniSat, CaDiCaL, Glucose, Kissat, MapleSAT — accepts
[DIMACS CNF](https://www.cs.utexas.edu/~marijn/SAT/) input and is built
around clause-level reasoning:

- **Boolean Constraint Propagation (BCP / unit propagation):** if every
  literal in a clause is falsified except one, that last one must be
  true. Almost all CDCL runtime is BCP.
- **Watched literals:** a clause data structure giving amortised O(1)
  per propagation regardless of clause size.
- **Conflict-driven clause learning (CDCL):** on conflict, derive a new
  clause summarising the reason and add it to the database.
- **VSIDS** and other heuristics score literals by frequency in
  recently-learnt clauses.

All of these are clause-shaped and don't apply to arbitrary `Formula`s.
So before handing a problem to a SAT solver, you translate it to CNF —
which is what Problem 7 sets up and Problem 9 (Note 05) consumes.


## 3. The grammar in the project text has a typo

The handout prints

```
CNF → Disjunct ∨ CNF
```

This is wrong twice; flag it if a grader asks.

1. **Wrong connective.** A *conjunctive* normal form is a conjunction of
   disjuncts, so the top-level connective must be `∧`, not `∨`. As
   written, this defines a *disjunctive* normal form (DNF) with
   one-literal conjuncts.
2. **No base case.** The right-hand side mentions `CNF` but never gives
   a non-recursive alternative, so the grammar is empty.

We fix it to

```
CNF → Disjunct
    | Disjunct ∧ CNF
```

— a non-empty conjunction of disjuncts — and code that. The Agda type
below mirrors this corrected grammar one-to-one. The comment block above
the definition in [`src/Solution.agda`](../src/Solution.agda#L187)
spells out the same fix.


## 4. The Agda definition

From [`src/Solution.agda`](../src/Solution.agda#L193) (lines 193–202):

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

Each constructor is one production:

- `lit ℓ` — single-literal clause; base case of `Disjunct`.
- `ℓ ∨d d` — prepend a literal to an existing clause; recursive case.
- `dis d` — one-clause CNF; base case of `CNF`.
- `d ∧c φ` — prepend a clause to an existing CNF; recursive case.

The `infixr` declarations make `ℓ₁ ∨d ℓ₂ ∨d lit ℓ₃` parse as
`ℓ₁ ∨d (ℓ₂ ∨d lit ℓ₃)`, matching the grammar's right-recursion. The
precedences aren't strictly needed (the operators work on different
types) but keep associativity consistent with `_∨_` / `_∧_` on raw
formulas.

### Why non-empty lists, not `List Literal` / `List Disjunct`?

Both types are essentially **non-empty lists**:

```
Disjunct ≅ List⁺ Literal
CNF      ≅ List⁺ Disjunct
```

We rule out empty cases at the *type* level:

- **The empty disjunction is `false`.** A zero-literal clause is
  vacuously unsatisfied, making every CNF containing it unsatisfiable —
  information better kept out of the syntax (and equational reasoning
  becomes awkward, e.g. `eval ρ ⟨⟩ = just false` for *any* ρ).
- **The empty conjunction is `true`.** A zero-clause CNF is vacuously
  satisfied. Same problem: special-casing everywhere.

Forcing non-emptiness means recursion in `eval-disjunct` and `eval-cnf`
always has something to look at, with no `if empty then …` branches. The
price is we can't express the two degenerate cases — but we don't need
them.

**Aside — empty clauses in real solvers.** Real SAT solvers *do* allow
the empty clause as the **unsatisfiability signal**: when CDCL derives
an empty learnt clause, the formula is UNSAT. So banning it is right for
*syntax* but the empty clause is a useful *runtime* object. Our DPLL
implementation handles unsatisfiability by returning `false` from the
recursive search rather than carrying around an empty clause.


## 5. CNF and arbitrary formulas are equi-expressive

**Theorem.** Every formula `φ` is logically equivalent to some CNF
formula `φ'` over the same variables.

**Proof sketch.** Two phases.

1. **NNF.** Convert `φ` to negation normal form (Note 02): push `¬`
   inwards using De Morgan's laws and double-negation until every `¬`
   sits on a variable. Linear-size.

2. **Distribution.** Now we have a formula built from literals using
   only `∧` and `∨`. Repeatedly apply

       a ∨ (b ∧ c)  ≡  (a ∨ b) ∧ (a ∨ c)
       (a ∧ b) ∨ c  ≡  (a ∨ c) ∧ (b ∨ c)

   to push every `∧` outside. Eventually every `∨` is below every `∧`.

That's the **naive CNF transformation**. Correct, but it can produce
exponentially-larger formulas — exactly the pathology Tseytin's
transformation (Note 06) avoids by introducing fresh variables for
subformulas.

We do *not* implement this conversion: Problem 7 takes CNF as given and
Problem 9 writes a solver for it. The fact that arbitrary formulas
reduce to CNF is the *reason* a CNF-only solver is not a restriction.


## 6. Worked example: the distribution blow-up

Take

```
(a ∧ b) ∨ (c ∧ d)
```

2 binary connectives, 4 variable occurrences. Distribute `∨` over `∧`:

```
(a ∧ b) ∨ (c ∧ d)
  ≡  ((a ∧ b) ∨ c) ∧ ((a ∧ b) ∨ d)         (distribute ∨ over the right ∧)
  ≡  ((a ∨ c) ∧ (b ∨ c)) ∧ ((a ∨ d) ∧ (b ∨ d))    (distribute on each side)
  ≡  (a ∨ c) ∧ (a ∨ d) ∧ (b ∨ c) ∧ (b ∨ d)        (drop redundant brackets)
```

Multiplicative effect: 2 × 2 = 4 clauses. Generalising,

```
(a₁ ∧ a₂ ∧ … ∧ aₙ) ∨ (b₁ ∧ b₂ ∧ … ∧ bₙ)
```

distributes into `n²` clauses `aᵢ ∨ bⱼ`, and

```
(a₁ ∧ … ∧ aₙ) ∨ (b₁ ∧ … ∧ bₙ) ∨ (c₁ ∧ … ∧ cₙ)
```

into `n³`. With `k` disjoined conjunctions of width `n`, you get `nᵏ` —
exponential. Hence Tseytin.

In our Agda spelling, the CNF version of the small example is

```agda
example-cnf : CNF
example-cnf =
    ( pos 0 ∨d lit (pos 2) )         -- a ∨ c
  ∧c ( pos 0 ∨d lit (pos 3) )        -- a ∨ d
  ∧c ( pos 1 ∨d lit (pos 2) )        -- b ∨ c
  ∧c dis ( pos 1 ∨d lit (pos 3) )    -- b ∨ d
```

(`a, b, c, d` encoded as variable indices `0, 1, 2, 3`).


## 7. Evaluation (Problem 8)

From [`src/Solution.agda`](../src/Solution.agda#L209) (lines 209–219):

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

Result type is `Maybe Bool`, the same partial-evaluation convention as
`eval` and `eval-nnf` (Note 02): `just b` means "fully decided with
truth value `b`", `nothing` means "I needed a variable ρ does not bind".

### `eval-disjunct`, line by line

- **Singleton `lit ℓ`**: defer to `eval-lit ρ ℓ`.
- **Cons `ℓ ∨d d`**: evaluate head and tail. If both `just _`, OR them;
  otherwise `nothing`.

Note: this is **strict** in both arguments. It does *not* short-circuit
"if the head is `just true`, the whole clause is `just true`". So
`eval-disjunct (pos 0 ∨d lit (pos 1))` under `ρ = [(0, true)]` returns
`nothing`, even though the clause is logically `true` — variable `1` is
unbound and our convention is "fully decided or nothing". This matches
`eval`, `eval-nnf`, and `eval-cnf`. (A solver can look harder; this
function just reads off the truth table.)

### `eval-cnf`, line by line

- **Singleton `dis d`**: defer to `eval-disjunct ρ d`.
- **Cons `d ∧c φ`**: evaluate head clause and tail. If both `just _`,
  AND them; otherwise `nothing`.

Same strictness caveat.

### Tiny worked example

Let

```agda
ρ : Assignment
ρ = (0 , true) ∷ (1 , false) ∷ (2 , true) ∷ []

φ : CNF
φ = (pos 0 ∨d lit (neg 1))            -- (x₀ ∨ ¬x₁)
   ∧c dis (neg 0 ∨d lit (pos 2))      -- (¬x₀ ∨ x₂)
```

First clause `(x₀ ∨ ¬x₁)` under ρ:
- `eval-lit ρ (pos 0) = just true`
- `eval-lit ρ (neg 1) = just (not false) = just true`
- so `eval-disjunct ρ … = just (true or true) = just true`.

Second clause `(¬x₀ ∨ x₂)`:
- `eval-lit ρ (neg 0) = just false`
- `eval-lit ρ (pos 2) = just true`
- so `dis (… ∨d lit (pos 2)) = just (false or true) = just true`.

Combine: `eval-cnf ρ φ = just (true and true) = just true`. φ is
satisfied by ρ.

Drop variable `2`: `ρ' = (0,true) ∷ (1,false) ∷ []`. The second clause
asks for `pos 2`, gets `nothing`, the whole second clause becomes
`nothing`. Then `just _ and nothing` falls into `_ | _ = nothing`. So
`eval-cnf ρ' φ = nothing`. Our `Maybe Bool` semantics is "decided iff
every leaf is bound" — the simple, uniform choice Problem 8 asks for.


## 8. CNF as a multiset of multisets

Because `∧` and `∨` are commutative, associative, and idempotent, the
*logical* meaning of a CNF is invariant under:

- reordering the clauses,
- reordering literals inside each clause,
- removing duplicate clauses,
- removing duplicate literals inside a clause.

So the most faithful semantic representation is a **set of sets of
literals**, or — keeping multiplicities for performance — a **multiset
of multisets**. That's what real solvers store: a clause database is an
array of clauses, each a small array of literal IDs. DIMACS is just a
serialisation:

```
p cnf 3 2
1 -2 0
-1 3 0
```

means "3 variables, 2 clauses; clause 1 is `x₁ ∨ ¬x₂`; clause 2 is
`¬x₁ ∨ x₃`" — terminator `0` separates clauses, order doesn't matter.

We deliberately do **not** use the multiset representation. Two reasons:

1. **The grammar is inductive and ordered.** Problem 7 asks us to model
   the *grammar*, which is right-recursive. Our `_∨d_` / `_∧c_`
   cons-cells mirror it exactly. A multiset would lose this.
2. **Pattern matching is easier on lists.** `eval-disjunct` decomposes
   head/tail; a Set/Multiset in Agda would need a representation choice
   (`AVL`, sorted lists) and propositional equality / decidable order
   baggage. None of that helps the toy DPLL solver, which is exponential
   anyway.

The cost is small: passes that *would* benefit from set semantics
(removing duplicate literals, recognising equal clauses) need extra
work. Our solver doesn't need any of that.

Extending toward a "real" SAT solver, the first refactor is usually
switching to a list-of-lists representation (perhaps `List (List
Literal)` with non-emptiness as invariant), because that's what
unit-propagation-with-watched-literals wants. The inductive
`Disjunct`/`CNF` types then become a thin wrapper for parsing and
theorem-statements.
