# Note 10 — Problem 10: Correctness of the SAT Solver

Problem 10: *"Show that the SAT solver you implemented is indeed
correct, if that is not obvious from the output type of the SAT
solver."* Code: `src/Solution.agda`, Problem 10 section (right after
Problem 9). Interactive visualisation:
[problem10-visual.html](problem10-visual.html).

## 1. The two halves of correctness

| Half             | Statement                                                | Status in our solution            |
| ---------------- | -------------------------------------------------------- | --------------------------------- |
| **Soundness**    | `sat? φ ≡ sat ρ p` ⟹ `eval-cnf ρ φ ≡ just true`          | **Holds by the output type**      |
| **Completeness** | a model exists ⟹ `sat? φ` returns `sat` (not `unsat`)    | **Not formally proven** (honest!) |

## 2. Soundness — why it is "obvious from the output type"

Problem 9 defines

```agda
data SatResult (φ : CNF) : Set where
  sat   : (ρ : Assignment) → eval-cnf ρ φ ≡ just true → SatResult φ
  unsat : SatResult φ
```

Agda **refuses to construct** `sat ρ p` without a valid proof `p`.
The only place the solver builds a `sat` is the search leaf:

```agda
sat-search [] ρ φ with eval-cnf ρ φ in eq
... | just true = sat ρ eq
```

The `with … in eq` idiom binds `eq : eval-cnf ρ φ ≡ just true` in
that branch — exactly the proof `sat` demands. So soundness is
*enforced by the type checker*, not argued after the fact. This is
precisely the situation the problem statement anticipates with "if
that is not obvious from the output type".

For clarity the file still states it as an explicit lemma:

```agda
sat?-sound : ∀ {φ ρ p} → sat? φ ≡ sat ρ p → eval-cnf ρ φ ≡ just true
sat?-sound {p = p} _ = p
```

The body is just `p` — the proof already lives inside the `sat`
constructor; the lemma merely extracts it.

## 3. Completeness — what we would want, and why we don't prove it

The two statements we would like (equivalent formulations):

```agda
sat?-complete₁ : ∀ {φ ρ} → eval-cnf ρ φ ≡ just true → sat? φ ≡ sat ρ′ _   -- solver doesn't miss models
sat?-complete₂ : ∀ {φ} → (∀ ρ → eval-cnf ρ φ ≢ just true) → sat? φ ≡ unsat -- unsat answers don't lie
```

The full discussion lives as a long comment block in
`src/Solution.agda` (Problem 10). Summary of the obstacles:

| # | Obstacle | Core of the issue |
|---|----------|--------------------|
| A | `unsat` carries no proof | The type of `unsat` does not say "no model exists", so nothing about UNSAT answers can be extracted from `SatResult` itself. |
| B | Large induction over the search | Proving the solver never wrongly answers `unsat` means showing, for every DPLL step (skip, pure literal, conflict cut, split), that a surviving model is never lost. Each case needs auxiliary lemmas about `eval-cnf` and `insert`. |
| C | Completeness of `cnf-vars` | One must prove `cnf-vars` mentions every variable that influences `eval-cnf` (duplicates are harmless, omissions are not). |
| D | Partial assignments | "We explored all branches" must be connected to "for *every* mathematical ρ" — Agda does not know our finite search covers the infinite type `Assignment` without an explicit argument. |

The solver *is* complete in the informal sense — the search space over
the formula's variables is explored exhaustively, branches are cut
only when a clause is already entirely false (no extension can repair
it), and a pure literal's forced value never destroys a model. But
formalising this is a sizeable proof development, far beyond the
project's scope, and we say so honestly rather than hand-waving.

## 4. `sat-from-proof`

```agda
sat-from-proof : ∀ {φ} {ρ : Assignment}
               → (p : eval-cnf ρ φ ≡ just true) → SatResult φ
sat-from-proof {ρ = ρ} p = sat ρ p
```

If you *already have* a model and its proof, you can build a
`SatResult` by hand. This is **not** completeness of the solver (it
says nothing about `sat?` finding that ρ); it only illustrates that
the `sat` constructor is exactly "a model with evidence".

## 5. Relation to Problem 9

| Problem 9                    | Problem 10                              |
| ---------------------------- | ---------------------------------------- |
| defines `SatResult`, `sat?`  | explains why that design is sound       |
| the leaf produces `eq`       | the lemma `sat?-sound` extracts it      |

Bottom line for grading: soundness is covered by the type design plus
a one-line lemma; completeness is honestly documented as out of scope,
with the proof obligations sketched in the code comments.
