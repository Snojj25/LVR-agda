# Note 05 — Problem 9: A SAT solver for CNF

Problem 9: a decision procedure for CNF satisfiability. Code:
`src/Solution.agda` lines 244–286. Prerequisites: notes 03 (CNF),
04 (Assoc).

## 1. The SAT problem

Given a propositional formula `φ` over `n` variables, **SAT** asks:
does there exist a truth assignment ρ making `⟦φ⟧ρ = true`?

If yes, `φ` is **satisfiable** and ρ is a **model**; if no, it is
**unsatisfiable** (UNSAT).

**SAT is NP-complete** (Cook–Levin, 1971/1973). In fact CNF-SAT —
even 3-CNF — is NP-complete, via the Tseytin-style transformation
(note 06). So unless P = NP, every SAT algorithm has worst-case
exponential running time; the game is doing dramatically better on
real-world inputs.

SAT is enormously useful in practice (hardware verification, planning,
software model checking, SMT, package dependency resolution, …).
Modern industrial solvers handle tens of millions of variables.

## 2. Naive truth-table search

The brute force: enumerate all `2ⁿ` assignments and evaluate. Sound
and complete, total cost `O(2ⁿ · |φ|)`. The recursive version that
follows is morally the same — except recursion lets us **stop early**
as soon as a partial assignment cannot extend to a model.

## 3. The DPLL splitting rule

The central move of the Davis–Putnam–Logemann–Loveland algorithm
(1962): for any variable `v` in `φ`,

> `φ` is satisfiable  ⟺  `φ[v ↦ true]` is satisfiable  *or*
> `φ[v ↦ false]` is satisfiable.

Picture: a binary search tree of partial assignments. Each internal
node branches on `v = true` / `v = false`; each leaf is a complete
assignment. At most `2ⁿ` leaves — the question is how many we
actually visit.

## 4. Two heuristics that make DPLL useful (sketch)

Pure splitting is correct but slow. Classical DPLL applies two
simplifications exhaustively before each branch:

- **Unit propagation (BCP).** If a clause has shrunk to a single
  literal `ℓ`, `ℓ` is *forced* — assign it and continue. In real
  instances, >90 % of all assignments come from BCP, not branching.
- **Pure literal elimination.** A literal `ℓ` is *pure* if `¬ℓ`
  doesn't occur. Setting `ℓ = true` only helps, so commit it.

Our solver implements *pure splitting only*. The two heuristics make
DPLL useful in practice; adding them in Agda requires a more careful
termination argument (see §7).

## 5. The Agda code

### 5.1 Collecting variable indices

```agda
lit-var : Literal → ℕ
lit-var (pos n) = n
lit-var (neg n) = n

dis-vars : Disjunct → List ℕ
dis-vars (lit ℓ)   = lit-var ℓ ∷ []
dis-vars (ℓ ∨d d)  = lit-var ℓ ∷ dis-vars d

cnf-vars : CNF → List ℕ
cnf-vars (dis d)   = dis-vars d
cnf-vars (d ∧c φ)  = dis-vars d ++ cnf-vars φ
```

All variable indices in `φ`, with duplicates. Once every variable in
`cnf-vars φ` is assigned, `φ` has no free variables, so `eval-cnf`
returns `just _`.

### 5.2 Dedup

```agda
mem? : ℕ → List ℕ → Bool
mem? _ []        = false
mem? n (m ∷ ms)  with n ≟ m
... | yes _ = true
... | no  _ = mem? n ms

dedup : List ℕ → List ℕ
dedup []        = []
dedup (n ∷ ns)  with mem? n (dedup ns)
... | true  = dedup ns
... | false = n ∷ dedup ns
```

Without dedup, branching on the same variable twice doubles work
(`insert` shadows, but we still explore both branches). Dedup is a
performance fix; correctness holds without it.

### 5.3 The recursion

```agda
sat-search : List ℕ → Assignment → CNF → Bool
sat-search [] ρ φ with eval-cnf ρ φ
... | just true  = true
... | _          = false
sat-search (v ∷ vs) ρ φ =
      sat-search vs (insert v true  ρ) φ
   or sat-search vs (insert v false ρ) φ
```

Read as: *`sat-search vs ρ φ` is `true` iff some extension of ρ
that assigns every variable in `vs` makes `φ` true.*

- **Base `vs = []`.** No variables left. If we started from
  `dedup (cnf-vars φ)`, ρ binds every variable of `φ` and `eval-cnf`
  is defined. Accept iff `just true`.
- **Recursive.** Branch on `v`: the `or` accepts if either extension
  works.

**Termination** is trivial: `vs` shrinks by one per call. Structural
recursion on a list — Agda's checker accepts immediately. We are
*not* recursing on `φ` or ρ.

### 5.4 Top-level

```agda
sat? : CNF → Bool
sat? φ = sat-search (dedup (cnf-vars φ)) empty φ
```

Collect variables, dedup, start with `empty`, hand off.

## 6. Soundness and completeness

**Soundness.** If `sat? φ = true`, some ρ models `φ`. By induction on
`length vs`: base case gives the witness; the inductive step
propagates the witness up through `or`.

**Completeness.** If some ρ* models `φ`, then `sat? φ = true`.
Stronger claim by induction on `length vs`: whenever ρ* extends the
current ρ and assigns every variable in `vs`, the corresponding
call returns `true`. Base case is `eval-cnf ρ φ = just true`;
recursive step picks the branch matching `ρ*(v)`.

Worst case `O(2ⁿ · |φ|)` where `n = length (dedup (cnf-vars φ))`.

## 7. Why full DPLL is awkward in Agda

`sat-search` is structurally recursive on a *shrinking variable list*
because we always branch and never simplify the formula. Adding BCP
or pure-literal breaks this: BCP shrinks *clauses* without
necessarily removing a variable per call.

The decreasing quantity becomes a lexicographic measure
`(length vs, size of φ)` — not directly accepted by Agda's checker.
The standard fix is **well-founded recursion** via `Acc _<_` from
`Induction.WellFounded`: encode the state's measure as a single `ℕ`
and supply a strict-decrease proof at every recursive call. Heavier
than structural recursion. For a teaching solver, pure splitting is
the right trade-off.

## 8. Beyond DPLL: a name to know

Modern solvers are **CDCL** (*conflict-driven clause learning*): on
hitting a falsified clause, analyse the conflict to derive a *learnt
clause*, then non-chronologically backtrack to the level where the new
clause forces a useful propagation. Combined with *watched literals*,
*VSIDS* heuristics, *restarts*, and *phase saving*, this scales to
millions of variables on structured inputs. Implementing it properly
is a semester-long project.
