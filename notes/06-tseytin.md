# Note 06 — The Tseytin Transformation: NNF → CNF in Linear Time

This note covers Problem 10: converting an NNF formula into an
equisatisfiable CNF using the *Tseytin transformation*. The Agda code
is in `src/Solution.agda`, lines 282–358. This is the final piece that
lets us run the SAT solver of Problem 9 on *arbitrary* input formulas.

Reading order so far:

- Note 01 — `Formula` (Problem 1).
- Note 02 — `NNF` and `Formula → NNF` (Problems 2, 3).
- Note 03 — `Disjunct`, `CNF`, and CNF evaluation (Problems 7, 8).
- Note 04 — `Assoc` / `Assignment` (Problem 4).
- Note 05 — the splitting-rule SAT solver (Problem 9).

After this note the pipeline

```
Formula  →[Problem 3]→  NNF  →[Problem 10]→  CNF  →[Problem 9]→  SAT/UNSAT
```

is complete: any propositional formula can be checked by `to-nnf`,
then `tseytin`, then `sat?`.

## 1. The naive approach: distribute ∨ over ∧

We already know how to push negations down (Note 02): an NNF has all
negations on variables, joined by `∧` and `∨`. To get CNF we need to
push `∨` *underneath* every `∧` via the distributive law

```
(a ∧ b) ∨ c   ≡   (a ∨ c) ∧ (b ∨ c)
a ∨ (b ∧ c)   ≡   (a ∨ b) ∧ (a ∨ c)
```

Applied recursively, any NNF becomes a CNF. The trouble is the size of
the result.

### A worked blow-up

Take the NNF

```
φₙ  =  (a₁ ∧ b₁)  ∨  (a₂ ∧ b₂)  ∨  …  ∨  (aₙ ∧ bₙ).
```

It has 2n literals — linear in n. Distributing for n = 2:

```
(a₁ ∧ b₁) ∨ (a₂ ∧ b₂)
  ≡  ((a₁ ∧ b₁) ∨ a₂)  ∧  ((a₁ ∧ b₁) ∨ b₂)
  ≡  ((a₁ ∨ a₂) ∧ (b₁ ∨ a₂))  ∧  ((a₁ ∨ b₂) ∧ (b₁ ∨ b₂))
```

— four clauses, *every choice of one literal from each conjunct*. In
general

```
φₙ  ≡  ⋀ { ℓ₁ ∨ ℓ₂ ∨ … ∨ ℓₙ  :  each ℓᵢ ∈ {aᵢ, bᵢ} }
```

so the CNF has exactly **2ⁿ** clauses of size n. For n = 30 that is
over a billion clauses — the conversion runs out of memory.

The lesson: equivalence-preserving CNF conversion can be exponential.
This is a fact about the smallest equivalent CNF for some formulas. So
for a *small* CNF we have to weaken what "preserves the formula" means.

## 2. Equivalence vs equisatisfiability

This is the central conceptual move of Tseytin.

Two formulas φ and ψ are **equivalent** (`φ ≡ ψ`) iff for *every*
assignment ρ,

```
eval ρ φ  =  eval ρ ψ.
```

Equivalent formulas have the *same set of models* and are
interchangeable in every context.

Two formulas φ and ψ are **equisatisfiable** iff

```
φ has at least one satisfying assignment    ⇔    ψ does.
```

This is much weaker. φ might have one model and ψ a hundred; ψ may use
brand-new variables not in φ. All that matters is "either both
satisfiable, or neither".

For SAT solving, equisatisfiability is exactly the right notion. The
solver only asks "does some assignment satisfy this?" — extra models
or variables don't matter as long as the yes/no verdict matches.

Naive distribution preserves equivalence at exponential cost. Tseytin
preserves only equisatisfiability but is **linear**. For SAT, a great
trade.

## 3. The idea of Tseytin

Imagine the parse tree of an NNF: leaves are literals, internal nodes
are `∧` or `∨`. Tseytin introduces, for every internal node, one
**fresh propositional variable** `x_φ` as an abbreviation: "let `x_φ`
mean *the value of the subformula at this node*".

For each internal node we *constrain* the abbreviation. If the node is

```
        φ  =  ψ_a  ∧  ψ_b
```

with abbreviations `x_φ`, `x_a`, `x_b` (or, if `ψ_a` is a literal
`ℓ`, we use `ℓ` directly), we add clauses encoding

```
x_φ   ↔   x_a  ∧  x_b.
```

Same for `∨`. Finally a single unit clause

```
x_root
```

asserts the abbreviation for the *whole formula* is true. The
conjunction of all those constraints is the Tseytin CNF.

Why no blow-up? We never duplicate any subformula. The naive approach
implicitly *copies* `(a₁ ∧ b₁)` into every clause it contributes to;
Tseytin gives it *one* name and refers to it. Every node turns into at
most three clauses of constant size.

## 4. Encoding `↔` as clauses

We need `x ↔ (a ∧ b)` (and the `∨` version) as CNF. Here `x`, `a`, `b`
are *literals* (children may have already been turned into literals).

### The conjunction case: `x ↔ (a ∧ b)`

A biconditional is two implications:

```
x ↔ (a ∧ b)   =   (x → a ∧ b)   ∧   (a ∧ b → x).
```

**Direction 1: `x → a ∧ b`.** Material implication `p → q` is `¬p ∨ q`,
and `x → (a ∧ b)` is `(x → a) ∧ (x → b)`. So this unrolls into **two
clauses**:

```
¬x ∨ a
¬x ∨ b
```

**Direction 2: `a ∧ b → x`.** That is `¬(a ∧ b) ∨ x`, which by De
Morgan is `¬a ∨ ¬b ∨ x`. **One clause** of size 3:

```
¬a ∨ ¬b ∨ x
```

Total: three clauses of sizes 2, 2, 3 — **7 literal occurrences**.

#### Truth-table verification (∧ case)

| x | a | b | a∧b | x↔(a∧b) | ¬x∨a | ¬x∨b | ¬a∨¬b∨x | clauses ∧'d |
|---|---|---|-----|---------|------|------|---------|-------------|
| 0 | 0 | 0 | 0   | 1       | 1    | 1    | 1       | 1           |
| 0 | 0 | 1 | 0   | 1       | 1    | 1    | 1       | 1           |
| 0 | 1 | 0 | 0   | 1       | 1    | 1    | 1       | 1           |
| 0 | 1 | 1 | 1   | 0       | 1    | 1    | **0**   | **0**       |
| 1 | 0 | 0 | 0   | 0       | **0**| 1    | 1       | **0**       |
| 1 | 0 | 1 | 0   | 0       | **0**| 1    | 1       | **0**       |
| 1 | 1 | 0 | 0   | 0       | 1    | **0**| 1       | **0**       |
| 1 | 1 | 1 | 1   | 1       | 1    | 1    | 1       | 1           |

The "x↔(a∧b)" and "clauses ∧'d" columns agree on every row.

### The disjunction case: `x ↔ (a ∨ b)`

Same dance:

**Direction 1: `x → a ∨ b`** is `¬x ∨ a ∨ b`. **One clause**, size 3.

**Direction 2: `a ∨ b → x`** is `(a → x) ∧ (b → x)`, i.e.
`(¬a ∨ x) ∧ (¬b ∨ x)`. **Two clauses**, sizes 2, 2.

So `x ↔ (a ∨ b)` becomes:

```
¬x ∨ a ∨ b
¬a ∨ x
¬b ∨ x
```

Three clauses of sizes 3, 2, 2 — again 7 literal occurrences.

#### Truth-table verification (∨ case)

| x | a | b | a∨b | x↔(a∨b) | ¬x∨a∨b | ¬a∨x | ¬b∨x | clauses ∧'d |
|---|---|---|-----|---------|--------|------|------|-------------|
| 0 | 0 | 0 | 0   | 1       | 1      | 1    | 1    | 1           |
| 0 | 0 | 1 | 1   | 0       | 1      | 1    | **0**| **0**       |
| 0 | 1 | 0 | 1   | 0       | 1      | **0**| 1    | **0**       |
| 0 | 1 | 1 | 1   | 0       | 1      | **0**| **0**| **0**       |
| 1 | 0 | 0 | 0   | 0       | **0**  | 1    | 1    | **0**       |
| 1 | 0 | 1 | 1   | 1       | 1      | 1    | 1    | 1           |
| 1 | 1 | 0 | 1   | 1       | 1      | 1    | 1    | 1           |
| 1 | 1 | 1 | 1   | 1       | 1      | 1    | 1    | 1           |

Columns match throughout.

## 5. Linearity — *the* point of Tseytin

Let `n = |φ|` be the number of nodes in the NNF tree. Every internal
node contributes **at most three clauses of at most three literals**.
Leaves contribute nothing (literals don't get a fresh abbreviation).
Plus one unit clause at the top.

So clauses ≤ `3 · (#internal nodes) + 1` and literal occurrences ≤
`9 · (#internal nodes) + 1`. Both `O(n)`.

Compare with the naive `2^n` clauses. Linearity is *the* point of
Tseytin — every modern SAT preprocessor uses some variant of it. The
price (extra variables, only equisatisfiability) is paid happily.

## 6. Walking through the Agda code

Open `src/Solution.agda` lines 282–358.

### `flip` — negate a literal

```agda
flip : Literal → Literal
flip (pos n) = neg n
flip (neg n) = pos n
```

`Literal` already wraps `pos`/`neg`, so we cannot prefix `¬`
syntactically — we produce the dual literal. We use `flip` when
building iff-clauses: a recursive call returns some literal `la`, and
we need its negation in a clause.

### `max-var` — find a guaranteed-fresh starting point

```agda
max-var : NNF → ℕ
max-var (lit (pos n)) = n
max-var (lit (neg n)) = n
max-var (a ∧n b)      = max-var a ⊔ max-var b
max-var (a ∨n b)      = max-var a ⊔ max-var b
```

(`_⊔_` is max on `ℕ`.) The result is the largest variable index in φ,
so `suc (max-var φ)` does **not** occur in φ. We hand that to
`tseytin-aux` as the first "next fresh" and increment as we go. Every
fresh variable is bigger than every original one — no clashes.

### `disjunct-of` and `cnf-of` — non-empty list builders

`Disjunct` and `CNF` (Note 03) are *non-empty* cons-lists:

```
Disjunct = Literal | Literal ∨d Disjunct
CNF      = Disjunct | Disjunct ∧c CNF
```

There is no "empty disjunct", so we cannot `foldr` a list of literals;
we take the first separately to seed the cons-list.

```agda
disjunct-of : Literal → List Literal → Disjunct
disjunct-of ℓ []        = lit ℓ
disjunct-of ℓ (m ∷ ms)  = ℓ ∨d disjunct-of m ms
```

Build a right-nested disjunction with head `ℓ` and tail `m ∷ ms`. If
the tail is empty, you get just the literal.

```agda
cnf-of : Disjunct → List Disjunct → CNF
cnf-of d []        = dis d
cnf-of d (e ∷ es)  = d ∧c cnf-of e es
```

Same idea, one type up: glue a non-empty list of disjuncts into a CNF.
Pure plumbing, nothing logical.

### `tseytin-aux` — the workhorse

```agda
tseytin-aux : ℕ → NNF → ℕ × Literal × List Disjunct
```

Given a "next fresh" `n` and an NNF `φ`, return `(n', top, cs)` where

- `n'` is the new "next fresh" — strictly greater than every variable
  used so far.
- `top : Literal` *represents the value of φ* in the output. Either an
  original literal (trivial case) or `pos x` for some fresh `x`.
- `cs : List Disjunct` are the clauses generated.

**Base case — literal.**

```agda
tseytin-aux n (lit ℓ) = n , ℓ , []
```

For a literal `ℓ` we do **nothing**: no fresh variable, no clauses, top
literal is `ℓ` itself. The optimisation from section 5: don't waste a
fresh variable on something already a literal. Allocating one would
still be correct but needlessly larger.

**Conjunction case.**

```agda
tseytin-aux n (a ∧n b) with tseytin-aux n a
... | n₁ , la , cs₁ with tseytin-aux n₁ b
...   | n₂ , lb , cs₂ =
            let x   = n₂
                n₃  = suc n₂
                c₁ = disjunct-of (neg x) (la ∷ [])
                c₂ = disjunct-of (neg x) (lb ∷ [])
                c₃ = disjunct-of (flip la) (flip lb ∷ pos x ∷ [])
            in n₃ , pos x , c₁ ∷ c₂ ∷ c₃ ∷ cs₁ ++ cs₂
```

Step by step:

1. Recurse on `a` with `n` → `(n₁, la, cs₁)`.
2. Recurse on `b` with the *updated* `n₁` → `(n₂, lb, cs₂)`. Crucial:
   passing `n₁` (not `n`) keeps `b`'s variables disjoint from `a`'s.
3. Allocate `x = n₂`, new fresh `n₃ = suc n₂`.
4. Build the three iff-clauses for `x ↔ (la ∧ lb)`:
   - `c₁ = ¬x ∨ la` — `x → la`.
   - `c₂ = ¬x ∨ lb` — `x → lb`.
   - `c₃ = ¬la ∨ ¬lb ∨ x` — `la ∧ lb → x`.
   Note `flip la`, `flip lb` to negate literals.
5. Return `n₃`, top `pos x`, and the three new clauses prepended to
   `cs₁ ++ cs₂`.

**Disjunction case.** Same shape, `∨` clauses:

```agda
tseytin-aux n (a ∨n b) with tseytin-aux n a
... | n₁ , la , cs₁ with tseytin-aux n₁ b
...   | n₂ , lb , cs₂ =
            let x   = n₂
                n₃  = suc n₂
                c₁ = disjunct-of (neg x) (la ∷ lb ∷ [])
                c₂ = disjunct-of (flip la) (pos x ∷ [])
                c₃ = disjunct-of (flip lb) (pos x ∷ [])
            in n₃ , pos x , c₁ ∷ c₂ ∷ c₃ ∷ cs₁ ++ cs₂
```

- `c₁ = ¬x ∨ la ∨ lb` — `x → la ∨ lb`.
- `c₂ = ¬la ∨ x` — `la → x`.
- `c₃ = ¬lb ∨ x` — `lb → x`.

Exactly the three clauses from section 4.

### `tseytin` — top-level

```agda
tseytin : NNF → CNF
tseytin φ with tseytin-aux (suc (max-var φ)) φ
... | _ , top , cs = cnf-of (lit top) cs
```

- Start "next fresh" at `suc (max-var φ)`, so no fresh variable
  collides with one in φ.
- Build the final CNF by `cnf-of (lit top) cs`: prepend the unit clause
  `top` asserting "the top representative is true", which by induction
  means "φ is true".

If `φ` was already a literal, `cs` is empty and `cnf-of (lit top) []
= dis (lit top)` — the CNF asserting that single literal.

## 7. Worked example: `(p ∧ q) ∨ (¬p ∧ r)`

Take

```
φ  =  (p ∧ q)  ∨  (¬p ∧ r)
```

with `p = 0`, `q = 1`, `r = 2`. So `max-var φ = 2`, first fresh is `3`.

Tree:

```
            ∨
           / \
          ∧   ∧
         / \ / \
        p  q ¬p r
```

**Step 1.** `tseytin-aux 3 (lit (pos 0))` → `(3, pos 0, [])`.

**Step 2.** `tseytin-aux 3 (lit (pos 1))` → `(3, pos 1, [])`.

**Step 3.** Left conjunction `p ∧ q`:

- recurse on `p`: `(3, pos 0, [])`, so `la = pos 0`.
- recurse on `q` with `n₁ = 3`: `(3, pos 1, [])`, so `lb = pos 1`.
- allocate `x = 3`, `n₃ = 4`.
- clauses (writing `xi` for `pos i`, `¬xi` for `neg i`):
  - `c₁ = ¬x3 ∨ x0`         (`x3 → p`)
  - `c₂ = ¬x3 ∨ x1`         (`x3 → q`)
  - `c₃ = ¬x0 ∨ ¬x1 ∨ x3`   (`p ∧ q → x3`)
- return `(4, pos 3, [c₁, c₂, c₃])`.

**Step 4.** Right conjunction `(¬p) ∧ r` with `n = 4`:

- recurse on `¬p`: `(4, neg 0, [])`, `la = neg 0`.
- recurse on `r`: `(4, pos 2, [])`, `lb = pos 2`.
- allocate `x = 4`, new fresh `5`.
- clauses:
  - `c₄ = ¬x4 ∨ ¬x0`        (`x4 → ¬p`; `la = neg 0`)
  - `c₅ = ¬x4 ∨ x2`         (`x4 → r`)
  - `c₆ = x0 ∨ ¬x2 ∨ x4`    (`¬p ∧ r → x4`)
- return `(5, pos 4, [c₄, c₅, c₆])`.

**Step 5.** Top `∨n`:

- left: `la = pos 3`. Right with `n = 4`: `lb = pos 4`.
- allocate `x = 5`, new fresh `6`.
- clauses:
  - `c₇ = ¬x5 ∨ x3 ∨ x4`    (`x5 → x3 ∨ x4`)
  - `c₈ = ¬x3 ∨ x5`         (`x3 → x5`)
  - `c₉ = ¬x4 ∨ x5`         (`x4 → x5`)
- return `(6, pos 5, [c₇, c₈, c₉, c₁, c₂, c₃, c₄, c₅, c₆])`.

(Order doesn't matter logically — CNF is just a conjunction.)

**Step 6.** `tseytin φ` prepends unit clause `lit (pos 5)`. Final CNF:

```
x5                       (top unit clause)
∧  ¬x5 ∨ x3 ∨ x4         (c₇)
∧  ¬x3 ∨ x5              (c₈)
∧  ¬x4 ∨ x5              (c₉)
∧  ¬x3 ∨ x0              (c₁)
∧  ¬x3 ∨ x1              (c₂)
∧  ¬x0 ∨ ¬x1 ∨ x3        (c₃)
∧  ¬x4 ∨ ¬x0             (c₄)
∧  ¬x4 ∨ x2              (c₅)
∧  x0 ∨ ¬x2 ∨ x4         (c₆)
```

10 clauses, 23 literal occurrences. The original NNF had 3 internal
nodes; we generated `3 × 3 + 1 = 10` clauses, each size at most 3.

Sanity check: `(p, q, r) = (1, 1, 0)` makes φ true. Set `x3 = 1, x4 =
0, x5 = 1` and all 10 clauses hold.

## 8. Equisatisfiability proof, sketch

Claim: `tseytin φ` is satisfiable iff `φ` is.

### From a model of φ to a model of `tseytin φ`

Suppose ρ satisfies φ. Extend ρ to ρ' by *defining* each fresh `x_ψ`
to be the truth value of subformula ψ under ρ:

```
ρ'(x_ψ)  :=  eval-nnf ρ ψ.
```

Check every clause under ρ':

- The three iff-clauses for `ψ = ψ_a ∧ ψ_b` encode `x_ψ ↔ x_ψ_a ∧
  x_ψ_b`. By construction `ρ'(x_ψ) = eval-nnf ρ ψ = eval-nnf ρ ψ_a ∧
  eval-nnf ρ ψ_b = ρ'(x_ψ_a) ∧ ρ'(x_ψ_b)`, so the biconditional holds.
  Same for ∨.
- The unit clause `x_root` evaluates to `eval-nnf ρ φ = true`.

Every clause is satisfied; ρ' models `tseytin φ`.

### From a model of `tseytin φ` to a model of φ

Suppose σ satisfies `tseytin φ`. Let ρ be σ's restriction to the
original variables. Claim: for every subformula ψ of φ,

```
σ(x_ψ)  =  eval-nnf ρ ψ.
```

By induction on ψ:

- If ψ is a literal `ℓ`, no fresh variable is allocated; `x_ψ` is `ℓ`
  itself, and both sides are ℓ's value under ρ.
- If ψ = ψ_a ∧ ψ_b, by IH `σ(x_ψ_a) = eval-nnf ρ ψ_a` and similarly
  for `b`. The three iff-clauses force `σ(x_ψ) = σ(x_ψ_a) ∧ σ(x_ψ_b) =
  eval-nnf ρ ψ`.
- ψ_a ∨ ψ_b is symmetric.

For ψ = φ: `σ(x_root) = eval-nnf ρ φ`. The top unit clause forces
`σ(x_root) = true`, hence `eval-nnf ρ φ = true`. ρ models φ.

So φ is satisfiable iff `tseytin φ` is — equisatisfiability.

## 9. Optimisations to be aware of

The textbook Tseytin we wrote is intentionally simple. Several
refinements give smaller CNFs in practice; not required but useful to
know.

### Plaisted–Greenbaum (polarity-aware encoding)

Look at `x ↔ (a ∧ b)`:

```
¬x ∨ a            -- direction "x → a ∧ b"
¬x ∨ b            -- direction "x → a ∧ b"
¬a ∨ ¬b ∨ x       -- direction "a ∧ b → x"
```

If `x` only appears positively *in the rest of the formula*, we never
need `a ∧ b → x` — `x` may "be true even when `a ∧ b` is false" with
nothing objecting. Symmetrically for negative-only. Plaisted–Greenbaum
walks polarity over the formula and emits only the needed half.
Roughly halves the clause count.

### Sharing repeated subformulas (DAG, not tree)

If the same subformula `ψ` appears twice, our algorithm encodes it
twice. A smarter version memoises and reuses the same fresh variable —
turning the tree into a DAG. Big win for circuit-like formulas with
shared structure.

### Skipping trivial subformulas

Our base case skips fresh-variable allocation for *literals*. One
could go further: detect a subformula already in CNF and splice its
clauses verbatim with one fresh variable asserting their conjunction.
For the project, the simple base case is fine.

## 10. Connecting back to SAT

Given an arbitrary `Formula φ`:

1. `to-nnf φ : NNF` (Note 02, Problem 3) — pushes negations down.
   *Equivalence-preserving*, *linear*.
2. `tseytin (to-nnf φ) : CNF` (this note, Problem 10) —
   *Equisatisfiability-preserving*, *linear*.
3. `sat? (tseytin (to-nnf φ)) : Bool` (Note 05, Problem 9) — DPLL-style
   solver. *Sound and complete*.

The composition is a satisfiability decision procedure for arbitrary
propositional formulas: step 1 a polarity walk, step 2 a recursion
emitting at most three clauses per node, step 3 the only place actual
search happens.

Each problem is a small transformation between carefully-chosen
intermediate representations (`Formula`, `NNF`, `CNF`), and *each
transformation is justified by a theorem* (equivalence or
equisatisfiability). That is what Problems 1–10 teach: refactor a
logical question through a chain of normal forms until brain-dead
search can solve it. Tseytin is the last and most clever link — the
one that makes "SAT-solve any formula" practical instead of
exponential.
