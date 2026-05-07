# Note 05 — Problem 9: A SAT solver for CNF

This is the deepest technical note in the series. Problem 9 implements a
*decision procedure* for CNF satisfiability. Even though the Agda code is
short — six small definitions plus a wrapper — it sits on top of a remarkable
amount of theory: the first NP-complete problem, the algorithmic template
behind every modern SAT/SMT engine, and several subtle termination and
completeness arguments.

Reading order: this note assumes you have read

- **note 03** — `Formula → NNF` conversion and the meaning of literals,
- **note 04** — partial assignments (`Assoc`, `lookup`, `insert`),
- **(after this one) note 06** — Tseytin transformation, which produces the
  CNFs the solver consumes.

The two pieces compose: Tseytin reduces an arbitrary propositional formula to
a linear-size, equisatisfiable CNF; `sat?` then decides that CNF.

---

## 1. The Boolean satisfiability problem (SAT)

Given a propositional formula `φ` over `n` variables `x₁,…,xₙ`, the **SAT
problem** asks:

> Does there exist a truth assignment `ρ : {x₁,…,xₙ} → {true,false}` such that
> `⟦φ⟧ρ = true`?

If yes, `φ` is **satisfiable** and `ρ` is a **model** (or **witness**).
If no, `φ` is **unsatisfiable** (UNSAT). Closely related questions:

- **VALID** — does *every* assignment make `φ` true? (`φ` is a *tautology*.)
- **EQUIV** — do `φ` and `ψ` agree on every assignment?
- **ENTAIL** — does every model of `φ` also satisfy `ψ`?

All four reduce to SAT (or its complement) in linear time:

- `φ` is valid  ⟺  `¬φ` is unsatisfiable.
- `φ ≡ ψ`       ⟺  `(φ ∧ ¬ψ) ∨ (¬φ ∧ ψ)` is unsatisfiable.
- `φ ⊨ ψ`       ⟺  `φ ∧ ¬ψ` is unsatisfiable.

So a SAT decider is a *universal* tool for classical propositional reasoning.

### Cook–Levin: SAT is NP-complete

Stephen Cook (1971) and, independently, Leonid Levin (1973) proved:

> **Theorem (Cook–Levin).** SAT is NP-complete.

Two halves.

**SAT is in NP.** A nondeterministic Turing machine guesses an assignment
`ρ ∈ {0,1}ⁿ` and verifies `⟦φ⟧ρ = true` in polynomial time — evaluation is a
walk over the syntax tree. Equivalently, a model is a polynomial-size
*certificate* checkable by a polynomial-time *verifier*.

**SAT is NP-hard.** Cook showed every NP problem reduces in polynomial time
to SAT via a generic *tableau* construction: from a nondeterministic
polynomial-time machine `M` and input `w`, build a formula `φ_{M,w}` whose
variables describe every cell of `M`'s tape at every step of an accepting
computation. Clauses encode

- the initial tape contents are `w`,
- exactly one symbol per cell per step,
- transitions of `M` are respected at every step,
- the final state is accepting.

Then `φ_{M,w}` is satisfiable iff `M` accepts `w`, with size polynomial in
`|w|` and `|M|`'s running time. Solving SAT in polynomial time would give
`P = NP`.

### CNF-SAT is also NP-complete

The Cook–Levin construction already produces CNF, even **3-CNF** (at most 3
literals per clause). A generic local trick — replacing every internal gate
by a fresh variable plus three constraint clauses, exactly the **Tseytin
transformation** of note 06 — turns an arbitrary formula into an
equisatisfiable 3-CNF in linear time and space. So `sat?`'s problem is itself
NP-complete.

**Practical takeaway.** Unless `P = NP`, any SAT algorithm has worst-case
exponential running time. The naive `2ⁿ` truth-table is the inevitable upper
bound on the *worst* case. The whole game is doing *dramatically better* on
real-world inputs, which are almost never worst-case.

---

## 2. Practical relevance

SAT is one of the most successful applied algorithms of the last 25 years.

- **Hardware verification.** Equivalence checking and bounded model checking
  of circuits reduce to enormous CNFs. Intel, ARM, AMD routinely solve
  problems with millions of variables daily.
- **Software model checking and bug finding.** Symbolic execution, bounded
  model checkers like CBMC, and verifying-compiler frameworks discharge path
  conditions via SAT/SMT.
- **Planning.** Classical AI planning (STRIPS, PDDL) is encoded as SAT in the
  *SATPLAN* family — variables stand for "action `a` is taken at step `t`".
- **Theorem proving.** SMT solvers (Z3, CVC5, Yices, MathSAT, ...) are
  **CDCL SAT solvers** with theory-specific procedures for arithmetic,
  arrays, bit-vectors, etc. layered on top.
- **Cryptanalysis.** Cipher round functions encode as CNF; SAT solvers
  attack reduced-round AES, DES, and stream ciphers.
- **Combinatorial design.** Graph coloring, scheduling, Sudoku, latin
  squares, Pythagorean triples — standard SAT benchmarks.
- **Dependency resolution.** `apt`, `dnf`, `opam`, modern Linux package
  managers, even `cargo` use SAT or PB-SAT solvers for version selection.

**State of the art today.** Annual SAT Competition winners close instances
with tens of millions of variables and clauses. The shared algorithmic
backbone is **CDCL** — *conflict-driven clause learning* — a heavily
engineered descendant of **DPLL**. The solver in this project is a
stripped-down DPLL without the practical heuristics; understanding it is the
right starting point.

---

## 3. Naive truth-table search

Before DPLL, understand the brute force we are optimising.

An assignment over `n` variables is a function `{1,…,n} → {true,false}`,
of which there are `2ⁿ`. A *complete* algorithm:

```
TruthTable(φ):
  for each ρ ∈ {true,false}ⁿ:
    if ⟦φ⟧ρ = true:
      return SAT (with witness ρ)
  return UNSAT
```

**Sound** (returns SAT only when a model exists) and **complete** (finds one
if any exists). Each iteration evaluates `φ` in `O(|φ|)`, so total time is
`O(2ⁿ · |φ|)`.

The `sat-search` of §6 is morally a recursive version — it builds the
assignment one variable at a time and explores both branches. Without the §5
heuristics it has the same `2ⁿ` worst case, *unavoidable* in general
(assuming `P ≠ NP`). What changes is that recursion lets us **stop early** as
soon as a partial assignment cannot extend to a model. The brute force above
cannot.

---

## 4. The DPLL splitting rule

The Davis–Putnam–Logemann–Loveland algorithm (1962) is the granddaddy of
SAT. Its central move is the **splitting rule** (a.k.a. **branching rule**
or *Shannon expansion*):

> For any variable `v` occurring in `φ`,
>
> `φ` is satisfiable  ⟺  `φ[v ↦ true]` is satisfiable  *or*
> `φ[v ↦ false]` is satisfiable.

In pseudocode:

```
Split(φ):
  if φ is trivially true:  return SAT
  if φ is trivially false: return UNSAT
  pick some variable v occurring in φ
  return Split(φ[v ↦ true]) ∨ Split(φ[v ↦ false])
```

Structurally identical to the truth-table loop — worst case still `2ⁿ`
leaves — but the tree is built *incrementally*. As soon as the partial
assignment falsifies a clause, the corresponding subtree collapses to
`UNSAT`. With sensible variable ordering, the pruning is often dramatic.

Mental picture: a binary **search tree** of partial assignments. Root is the
empty assignment. Every internal node has two children (`v=true`,
`v=false`). A leaf is reached when `φ` simplifies to a constant. At most
`2ⁿ` leaves; the question is how many we actually visit.

The Agda solver implements exactly this splitting rule.

---

## 5. Two key heuristics: BCP and pure-literal

Plain splitting is already an algorithm, but not yet "DPLL" historically.
Two simplification rules — applied *exhaustively* before each branch — make
a vast practical difference.

### 5.1 Unit propagation (Boolean Constraint Propagation, BCP)

If, after substitutions, a clause has only one remaining literal, that
literal is **forced**: setting it true is the only way to avoid falsifying
the clause, so we may commit without losing models.

> **Unit rule.** If `φ` contains a clause `{ℓ}`, replace `φ` by
> `φ[ℓ ↦ true]` and continue.

Apply repeatedly. Propagation cascades: a forced assignment may shrink other
clauses to unit, forcing more assignments. In typical industrial CNFs more
than 90 % of all assignments come from BCP, not branching.

**Worked example.** Take

```
φ = (x₁ ∨ x₂ ∨ ¬x₃) ∧ (x₁) ∧ (¬x₁ ∨ x₂) ∧ (¬x₂ ∨ x₃)
```

`(x₁)` is unit. Set `x₁ = true`; clauses containing `x₁` are satisfied and
dropped, `¬x₁` is removed from clauses containing it:

```
φ' = (x₂ ∨ ¬x₃) ∧ (x₂) ∧ (¬x₂ ∨ x₃)
```

`(x₂)` is unit. Set `x₂ = true`:

```
φ'' = (x₃)
```

`(x₃)` is unit. Set `x₃ = true`. Empty clause set: SAT, model
`{x₁,x₂,x₃} = {T,T,T}`. We never branched.

The *watched literals* data structure makes BCP almost free: each clause has
two watched literals, revisited only when one is falsified. This is one of
the engineering tricks that pushed CDCL solvers from "thousands" to
"millions" of variables.

### 5.2 Pure literal elimination

A literal `ℓ` is **pure** in `φ` if `¬ℓ` does not occur. Setting `ℓ = true`
threatens no clause; it can only help.

> **Pure literal rule.** If `ℓ` is pure in `φ`, replace `φ` by
> `φ[ℓ ↦ true]`.

This eliminates `ℓ`'s variable and removes every clause containing `ℓ`.

**Worked example.** In

```
φ = (x₁ ∨ x₂) ∧ (x₂ ∨ ¬x₃) ∧ (x₁ ∨ ¬x₃)
```

`x₁` is pure (no `¬x₁`). Set `x₁ = true`; clauses 1 and 3 vanish. Remainder
`(x₂ ∨ ¬x₃)` has `x₂` and `¬x₃` both pure. Setting both true gives an empty
CNF. SAT, model `{T,T,F}`. No branching.

Pure-literal is *less* important than BCP in practice, because CDCL search
constantly adds learnt clauses (§9), which destroys purity. Many modern
solvers drop the rule entirely. For **textbook DPLL** and intuition, it
matters.

---

## 6. Walk-through of the Agda code

Now Problem 9 line by line, in `src/Solution.agda` around lines 230–280.
The solver does *not* implement BCP or pure-literal: it is *pure splitting*,
the simplest correct DPLL-shaped algorithm.

### 6.1 Collecting variable indices

```agda
lit-var : Literal → ℕ
lit-var (pos n) = n
lit-var (neg n) = n
```

A literal is `pos n` (i.e. `xₙ`) or `neg n` (i.e. `¬ xₙ`); either way the
underlying variable is `n`.

```agda
dis-vars : Disjunct → List ℕ
dis-vars (lit ℓ)   = lit-var ℓ ∷ []
dis-vars (ℓ ∨d d)  = lit-var ℓ ∷ dis-vars d

cnf-vars : CNF → List ℕ
cnf-vars (dis d)   = dis-vars d
cnf-vars (d ∧c φ)  = dis-vars d ++ cnf-vars φ
```

`cnf-vars φ` returns all variable indices in `φ`, **with duplicates**. The
splitting rule needs to know *which* variables to branch on; `sat-search`
recurses on this list, removing one variable per call. The list's length
bounds the search-tree depth.

The list also defines a "complete" assignment: once every variable in
`cnf-vars φ` is assigned, `φ` has no free variables, so `eval-cnf` returns
`just _`, never `nothing`. For closed `φ`, this is the natural notion of
totality.

### 6.2 `mem?` and `dedup`

```agda
mem? : ℕ → List ℕ → Bool
mem? _ []        = false
mem? n (m ∷ ms)  with n ≟ m
... | yes _ = true
... | no  _ = mem? n ms
```

Standard linear-time membership using `_≟_` from `Data.Nat`. The stdlib
`any (_≟_ n) ms` works, but rolling our own keeps the type in `Bool` rather
than `Dec`/`Any`, avoiding lifts at every site.

```agda
dedup : List ℕ → List ℕ
dedup []        = []
dedup (n ∷ ns)  with mem? n (dedup ns)
... | true  = dedup ns
... | false = n ∷ dedup ns
```

`dedup` removes duplicates: `[1,2,1,3,2,1] ↦ [1,2,3]` (order
implementation-defined). Two reasons:

1. **Avoid wasted work.** Without dedup, branching on the same variable
   twice doubles work — `(insert v true ρ)` shadows the previous binding and
   re-explores the same subspace. Worst case blows up by `2ᵏ` for `k`
   duplicates.
2. **Clean termination metric.** With dedup, list length equals the number
   of *distinct* free variables — the natural exponent.

(Soundness still holds without dedup: `insert` is first-match-wins, so a
second binding is a no-op for `lookup` unless it changes the value, in which
case the path evaluates to `false` anyway. Dedup is a performance fix, not a
correctness one.)

### 6.3 The recursion: `sat-search`

```agda
sat-search : List ℕ → Assignment → CNF → Bool
sat-search [] ρ φ with eval-cnf ρ φ
... | just true  = true
... | _          = false
sat-search (v ∷ vs) ρ φ =
      sat-search vs (insert v true  ρ) φ
   or sat-search vs (insert v false ρ) φ
```

The heart of the solver. Read the type as:

> `sat-search vs ρ φ` returns `true` iff some extension of `ρ` that assigns
> every variable in `vs` makes `φ` true.

Two cases.

**Base `vs = []`.** No variables left. If we started from
`dedup (cnf-vars φ)`, `ρ` is total over `cnf-vars φ`, so `eval-cnf ρ φ` is
defined. Accept iff `just true`. The catch-all `_ → false` covers:

- `just false` — current assignment falsifies `φ`,
- `nothing` — `φ` mentions an unassigned variable (impossible if `vs` was
  correctly seeded).

**Recursive `vs = v ∷ vs'`.** Branch on `v`: left disjunct with `v ↦ true`,
right with `v ↦ false`. The `or` accepts if either extension works.

**Termination.** Trivial: `vs` shrinks by exactly one per call, base fires
when empty. **Structural recursion on a list** — Agda's termination checker
accepts without help. We are *not* recursing on `φ` (unchanged) nor on `ρ`
(grows in both calls). The decreasing parameter is the first.

### 6.4 Top-level wrapper: `sat?`

```agda
sat? : CNF → Bool
sat? φ = sat-search (dedup (cnf-vars φ)) empty φ
```

Collect variables, deduplicate, start with the empty assignment, hand off.
Result is `true` iff `φ` is satisfiable. ~30 lines total.

---

## 7. Soundness, completeness, termination — informally

### Soundness

> If `sat? φ = true`, there exists `ρ` with `eval-cnf ρ φ = just true`.

*Sketch.* By induction on `length vs`:

- `vs = []`: returning `true` means `eval-cnf ρ φ = just true`, so `ρ` is the
  witness.
- `vs = v ∷ vs'`: result is `b₁ or b₂`. If `true`, one of `b₁, b₂` is `true`,
  and by IH the corresponding extension `(insert v _ ρ)` admits a witness —
  also a witness for `ρ` extended one step.

Starting from `ρ = empty`, the witness is total over all variables of `φ`. ∎

### Completeness

> If `eval-cnf ρ* φ = just true` for some `ρ*`, then `sat? φ = true`.

*Sketch.* By induction on `length vs`, prove the stronger claim:

> *Whenever* `ρ*` extends current `ρ` and assigns every variable in `vs`,
> if `eval-cnf ρ* φ = just true`, then `sat-search vs ρ φ = true`.

- **`vs = []`:** `ρ* = ρ` on every variable in `cnf-vars φ`, so
  `eval-cnf ρ φ = just true`; base returns `true`.
- **`vs = v ∷ vs'`:** by `ρ*(v)`, either `ρ*` extends `(insert v true ρ)` or
  `(insert v false ρ)`; the corresponding call is `true` by IH, so the `or`
  is `true`.

Specialise to `vs = dedup (cnf-vars φ)`, `ρ = empty`: any model `ρ*`
trivially extends `empty` and assigns every variable. ∎

### Termination

Already discussed: structural recursion on the first argument. The recursion
tree has at most `2ⁿ` leaves where `n = length (dedup (cnf-vars φ))`, total
work `O(2ⁿ · |φ|)`.

---

## 8. Pseudocode for full DPLL — and why Agda finds it hard

Full classical DPLL:

```
DPLL(φ):
  // 1. Boolean Constraint Propagation
  while φ has a unit clause {ℓ}:
    φ ← φ[ℓ ↦ true]
    if φ contains the empty clause: return UNSAT

  // 2. Pure literal elimination
  while φ has a pure literal ℓ:
    φ ← φ[ℓ ↦ true]

  // 3. Termination conditions
  if φ is empty (no clauses): return SAT
  if φ contains the empty clause: return UNSAT

  // 4. Branching
  pick a variable v occurring in φ      // heuristic
  return DPLL(φ ∧ {v}) or DPLL(φ ∧ {¬v})
```

Each `φ[ℓ ↦ true]` deletes clauses containing `ℓ` and removes `¬ℓ` from the
rest. Eventually we run out of clauses (SAT), produce an empty clause
(UNSAT), or branch.

### Why this is awkward in Agda

`sat-search` is structurally recursive on a *shrinking variable list*
because we always branch and never simplify the formula. Add BCP or
pure-literal and the variable list no longer decreases cleanly: BCP shrinks
*clauses* without necessarily removing a variable per call.

Full DPLL is no longer structurally recursive on a single argument. What
decreases is a **multi-component measure**:

  `μ(vs, φ) = (length vs, total size of φ)`

ordered lexicographically: BCP keeps `length vs` constant but strictly
decreases formula size; branching strictly decreases `length vs`. Agda's
checker accepts strict decreases on a single argument out of the box, but
lex measures need extra plumbing.

The standard fix is **well-founded recursion**. `Data.Nat.Induction`
provides:

```agda
<-wellFounded : WellFounded _<_
```

and a helper

```agda
wfRec : (P : ℕ → Set) → (∀ n → (∀ m → m < n → P m) → P n) → ∀ n → P n
```

Express your function as `wfRec` over the *measure* `μ`: pack state into a
single `n = encode(vs, φ)`, prove every recursive call uses a strictly
smaller measure, feed to `wfRec`. The encoding is fiddly; production Agda
typically uses the *acc* predicate from `Induction.WellFounded` directly:

```agda
sat-bcp : (vs : List ℕ) (φ : CNF) → Acc _<_ (μ vs φ) → Bool
sat-bcp vs φ (acc rs) = ...
  -- in each recursive call, supply  rs (μ vs' φ') (proof : μ vs' φ' < μ vs φ)
```

Heavier than structural splitting. For a *teaching* solver, pure splitting
is the right trade-off. For a *competitive* solver, you would write it in
C++ and *prove* its correctness in Agda/Coq/Isabelle.

---

## 9. Beyond DPLL: CDCL in three paragraphs

Modern SAT solvers are **CDCL**: *conflict-driven clause learning*. The key
innovation, due to Marques-Silva and Sakallah (GRASP, 1996), refined by
Moskewicz et al. (Chaff, 2001) and Eén and Sörensson (MiniSat, 2003): when
you hit a conflict — a partial assignment falsifying some clause — instead
of backtracking one level, *analyse* the conflict to derive a **learnt
clause** summarising *why* the assignment was bad, then jump back many
levels at once to where the new clause forces a useful unit propagation.
This is **non-chronological backtracking** (backjumping).

The rest of the modern toolkit:

- **Watched literals** (Chaff, 2001) — clause-watching makes BCP almost
  free: untouched unless one of two "watches" is falsified.
- **Activity-based heuristics (VSIDS)** — variable scores rise on appearance
  in recently-learnt clauses, decay over time. Branch on the highest-score
  variable to adapt to currently-hard parts of the formula.
- **Restarts** — after a conflict budget, drop the trail and start over,
  *keeping the learnt clauses*. Escapes bad regions and lets new VSIDS
  scores guide the next phase.
- **Phase saving** — on restart, remember each variable's last-assigned
  Boolean and reuse as default polarity.
- **Clause-database management** — periodically prune learnt clauses by
  utility (LBD, Glucose, 2009).

Breathtakingly effective on structured industrial inputs. On uniformly
random 3-SAT near the satisfiability threshold, CDCL is *less* of a win;
stochastic local search (WalkSAT, ProbSAT) takes over.

For a project at this level, knowing the names and rough shape of these
ideas is enough; implementing one properly is a semester-long undertaking.

---

## 10. Complexity remarks: the SAT landscape

General SAT is NP-complete, but several restricted versions live on either
side of the `P / NP-complete` line.

| Class      | Each clause is …                            | Status       | Algorithm                                                  |
| ---------- | ------------------------------------------- | ------------ | ---------------------------------------------------------- |
| SAT        | arbitrary (after CNF conversion)            | NP-complete  | DPLL / CDCL                                                |
| 3-SAT      | a disjunction of *exactly* 3 literals       | NP-complete  | DPLL / CDCL; classical reduction target                    |
| 2-SAT      | a disjunction of *at most* 2 literals       | **in P**     | Linear time via implication graph + SCC (Aspvall, Plass, Tarjan, 1979) |
| Horn-SAT   | at most one *positive* literal per clause   | **in P**     | Linear time by **unit propagation alone**                  |
| XOR-SAT    | each clause is a parity (`xor`) constraint  | **in P**     | Gaussian elimination over `GF(2)`                          |
| Renamable Horn | Horn after flipping some literal polarities | in P     | linear time                                                |

The Horn case is striking: **Horn-SAT is solved *entirely* by repeated unit
propagation**. Every Horn formula either has a unique minimal model BCP
discovers in linear time, or hits an empty clause (UNSAT). That is why BCP
is the most important DPLL rule — on a Horn subformula, it is *complete*.
In general SAT it is not, but the closer your formula is to "horn-like" the
more BCP carries the day.

The P / NP-complete boundary is sharp: adding a *single* third literal, or
removing the "at-most-one-positive" restriction, jumps from linear to
exponential.

The CNF that `sat?` accepts is unrestricted, so the worst case is genuinely
NP-complete. Most real instances are not adversarial; they have structure
DPLL/CDCL exploits beautifully.
