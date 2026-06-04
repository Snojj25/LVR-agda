# Note 09 — Problem 9: A SAT Solver for CNF (DPLL-style)

Problem 9: a satisfiability solver for CNF. Code: `src/Solution.agda`,
Problem 9 section. Prerequisites: notes 07 (CNF), 04 (assignments).
Interactive visualisation: [problem9-visual.html](problem9-visual.html).

## 1. The SAT problem

Given a propositional formula `φ`, **SAT** asks: does there exist a
truth assignment ρ making `⟦φ⟧ρ = true`?

If yes, `φ` is **satisfiable** and ρ is a **model**; if no, it is
**unsatisfiable** (UNSAT).

**SAT is NP-complete** (Cook–Levin, 1971/1973) — even restricted to
3-CNF. So unless P = NP, every SAT algorithm has worst-case
exponential running time; the game is doing dramatically better on
real-world inputs. SAT is enormously useful in practice (hardware
verification, planning, model checking, SMT, package dependency
resolution, …); modern industrial solvers handle millions of
variables.

## 2. What the problem asks for

> *"It should output either an assignment such that evaluating the
> formula at that assignment evaluates to true or that no such
> assignment exists."*

So a bare `Bool` is not enough — the answer must *carry the model*.
We go one step further and make the result type carry a **proof**:

```agda
data SatResult (φ : CNF) : Set where
  sat   : (ρ : Assignment) → eval-cnf ρ φ ≡ just true → SatResult φ
  unsat : SatResult φ
```

- `SatResult φ` is a **dependent type** — a different type for each
  formula `φ`.
- The `sat` constructor demands an assignment ρ *and* a proof
  `p : eval-cnf ρ φ ≡ just true`. Agda will not let the solver claim
  "satisfiable" without evidence.
- `unsat` carries nothing — it is only a flag (see note 10 for what
  this means for correctness).

## 3. The algorithm: DPLL-style search

The core of the Davis–Putnam–Logemann–Loveland algorithm (1962) is the
**splitting rule**: for any variable `v` of `φ`,

> `φ` is satisfiable ⟺ `φ[v ↦ true]` is satisfiable *or*
> `φ[v ↦ false]` is satisfiable.

Picture a binary tree of partial assignments; the question is how much
of it we can avoid visiting. Our solver adds two classic improvements
on top of plain splitting:

1. **Conflict pruning.** After each assignment, check whether some
   clause has become *entirely false* under the current partial ρ.
   If so, no extension of ρ can ever satisfy `φ` — cut the branch
   immediately instead of filling in the remaining variables.
2. **Pure literal rule.** If a variable occurs with only one polarity
   in `φ` (only `pos v`, or only `neg v`), setting it to that polarity
   can only help. We commit to the single helpful value and skip the
   other branch entirely.

(Full DPLL also has *unit propagation* — assigning the last undecided
literal of an almost-false clause without branching. We get a weaker
form of its effect for free: choosing the wrong value for such a
literal falsifies the clause, and conflict pruning cuts that branch
one step later.)

**A key design decision: the formula is never rewritten.** Textbook
DPLL simplifies `φ` as it goes (deleting satisfied clauses, shrinking
false literals out of clauses). We keep `φ` fixed and only grow ρ.
Two payoffs:

- *Termination is trivial* — we recurse on the shrinking list of
  variables, never on a rewritten formula (structural recursion, no
  well-founded machinery needed).
- *The proof falls out by itself* — at the leaf we simply run
  `eval-cnf ρ φ` on the original formula, and `with … in eq` hands us
  exactly the proof that `sat` requires.

## 4. The code

### Collecting variables

```agda
lit-var : Literal → ℕ
dis-vars : Disjunct → List ℕ
cnf-vars : CNF → List ℕ
```

All variable indices occurring in `φ`, *with duplicates* — the search
simply skips a variable that is already assigned, so deduplication is
unnecessary. Once every variable in `cnf-vars φ` is assigned,
`eval-cnf ρ φ` is guaranteed to return `just _` (no unbound variable
can produce `nothing`).

### Conflict detection

```agda
lit-false? : Assignment → Literal → Bool        -- literal known false?
clause-conflict? : Assignment → Disjunct → Bool -- ALL literals false?
cnf-conflict? : Assignment → CNF → Bool         -- SOME clause all-false?
```

`clause-conflict?` is the conjunction of `lit-false?` over the clause;
`cnf-conflict?` is the disjunction of `clause-conflict?` over the
clauses. Note these are plain `Bool` tests — they guide the search
only, so they need no proofs.

### Pure literal detection

```agda
pure-value : ℕ → CNF → Maybe Bool
pure-value v φ with cnf-pos? v φ | cnf-neg? v φ
... | true  | false = just true      -- occurs only positively
... | false | true  = just false     -- occurs only negatively
... | _     | _     = nothing        -- mixed → not pure
```

built from `pos-occ?`/`neg-occ?` (does this literal mention `v` with
this polarity?) lifted over disjuncts (`dis-pos?`/`dis-neg?`) and the
whole CNF (`cnf-pos?`/`cnf-neg?`).

### The search: three mutually recursive functions

```agda
sat-search : List ℕ → Assignment → (φ : CNF) → SatResult φ
decide     : ℕ → List ℕ → Assignment → (φ : CNF) → SatResult φ
try-assign : ℕ → Bool → List ℕ → Assignment → (φ : CNF) → SatResult φ

sat-search []       ρ φ with eval-cnf ρ φ in eq
... | just true = sat ρ eq                 -- leaf: eq IS the proof
... | _         = unsat
sat-search (v ∷ vs) ρ φ with lookup v ρ
... | just _  = sat-search vs ρ φ          -- already assigned → skip
... | nothing = decide v vs ρ φ

decide v vs ρ φ with pure-value v φ
... | just b  = try-assign v b vs ρ φ      -- pure → one branch only
... | nothing with try-assign v true vs ρ φ
...   | sat ρ′ p = sat ρ′ p                -- split: true first,
...   | unsat    = try-assign v false vs ρ φ   -- then false

try-assign v b vs ρ φ with cnf-conflict? (insert v b ρ) φ
... | true  = unsat                        -- conflict → prune branch
... | false = sat-search vs (insert v b ρ) φ

sat? : (φ : CNF) → SatResult φ
sat? φ = sat-search (cnf-vars φ) empty φ
```

Roles:

- **`sat-search`** walks the variable list. At the leaf (`[]`) it
  evaluates the formula; `with … in eq` binds
  `eq : eval-cnf ρ φ ≡ just true` in the `just true` branch, which is
  exactly what the `sat` constructor needs. Already-assigned variables
  (duplicates in `cnf-vars`) are skipped.
- **`decide`** picks the strategy for an unassigned variable: pure
  literal (one branch) or splitting (both branches, `true` first).
- **`try-assign`** extends ρ with `v ↦ b`, but first checks for a
  conflict; a conflicting branch is hopeless and is cut on the spot.

### Termination

Each cycle `sat-search (v ∷ vs) → decide v vs → try-assign v b vs →
sat-search vs` strictly shrinks the variable list, and `φ` never
changes. Agda's structural termination checker accepts this directly.

## 5. A worked run

Take `φ = (x₀ ∨ ¬x₁)`, i.e. `dis (pos 0 ∨d lit (neg 1))`.

1. `cnf-vars φ = 0 ∷ 1 ∷ []`; start `sat-search (0 ∷ 1 ∷ []) [] φ`.
2. `v = 0` is unassigned → `decide`. `pure-value 0 φ = just true`
   (only positive occurrence) — **pure literal**, single branch.
   No conflict → ρ = `(0 , true) ∷ []`.
3. `v = 1` is unassigned → `decide`. `pure-value 1 φ = just false`
   (only negative) — pure again. No conflict →
   ρ = `(0 , true) ∷ (1 , false) ∷ []`.
4. Leaf: `eval-cnf ρ φ = just (true or true) = just true` →
   `sat ρ eq`.

No splitting was ever needed — both variables were pure. For an
unsatisfiable input such as `x₀ ∧ ¬x₀` (where `x₀` is *not* pure), the
solver splits on `x₀`, and *both* `try-assign` calls hit an immediate
conflict, so the answer is `unsat` without ever reaching a leaf.

## 6. Complexity, honestly

Worst case is still `O(2ⁿ)` branches — SAT is NP-complete, and pure
literals/conflicts are heuristics, not a cure. The point of the design
is (a) the heuristics prune realistic inputs well, and (b) the result
type makes every `sat` answer self-certifying (note 10).

## 7. Beyond DPLL: a name to know

Modern solvers are **CDCL** (*conflict-driven clause learning*): on
hitting a falsified clause they derive a *learnt clause* and backtrack
non-chronologically. Combined with watched literals, VSIDS heuristics,
restarts, and phase saving, this scales to millions of variables.
Implementing it properly is a semester-long project; our solver keeps
the proof-carrying simplicity instead.
