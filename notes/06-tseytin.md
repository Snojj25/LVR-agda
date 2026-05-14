# Note 06 — The Tseytin Transformation: NNF → CNF in Linear Time

Problem 10: converting NNF into an equisatisfiable CNF in linear size.
Code: `src/Solution.agda` lines 295–365. This completes the pipeline

```
Formula  →[Problem 3]→  NNF  →[Problem 10]→  CNF  →[Problem 9]→  SAT/UNSAT
```

## 1. Why not just distribute?

The obvious NNF-to-CNF conversion pushes `∨` underneath `∧` via

```
a ∨ (b ∧ c) ≡ (a ∨ b) ∧ (a ∨ c)
```

Correct but can blow up exponentially. Take

```
φₙ = (a₁ ∧ b₁) ∨ (a₂ ∧ b₂) ∨ ⋯ ∨ (aₙ ∧ bₙ)        -- size 2n
```

Distribution produces `2ⁿ` clauses — one per choice of one literal
from each conjunct. For `n = 30` that's a billion clauses.

So equivalence-preserving CNF conversion can be exponential. To stay
linear, we have to weaken what "preserves the formula" means.

## 2. Equivalence vs equisatisfiability

- φ and ψ are **equivalent** if `eval ρ φ = eval ρ ψ` for every ρ —
  same set of models.
- φ and ψ are **equisatisfiable** if "φ has a model ⟺ ψ has one".
  Much weaker; ψ may use fresh variables, may have many more models.

For SAT we only ask "is there *some* model?" — equisatisfiability is
exactly what matters. Tseytin gives a linear-size equisatisfiable
CNF.

## 3. The idea

For every internal node of the NNF tree, introduce one **fresh
variable** `x_φ` as an abbreviation: *"`x_φ` means the value of the
subformula at this node"*. For a node `φ = ψ_a ∧ ψ_b` add clauses
encoding

```
x_φ  ↔  x_ψ_a  ∧  x_ψ_b
```

(and similarly for `∨`). Finally, one unit clause `x_root` asserts
the whole formula is true.

Why no blow-up? We never duplicate subformulas — each gets *one* name
and clauses refer to it. Every node yields at most three constant-size
clauses.

## 4. Encoding `↔` as clauses

### Conjunction: `x ↔ (a ∧ b)`

Split into two implications:

- `x → (a ∧ b)`  =  `(¬x ∨ a) ∧ (¬x ∨ b)`
- `(a ∧ b) → x`  =  `¬a ∨ ¬b ∨ x`

Three clauses of sizes 2, 2, 3.

### Disjunction: `x ↔ (a ∨ b)`

- `x → (a ∨ b)`  =  `¬x ∨ a ∨ b`
- `(a ∨ b) → x`  =  `(¬a ∨ x) ∧ (¬b ∨ x)`

Three clauses of sizes 3, 2, 2.

## 5. Linearity

Let `n` be the number of NNF nodes. Each internal node contributes at
most 3 clauses of at most 3 literals; leaves contribute nothing
(literals don't need an abbreviation); plus one unit clause at the
top. So clauses ≤ `3·n + 1` and total literal occurrences ≤ `9·n + 1`.
Both `O(n)`. Versus the `2ⁿ` of naive distribution.

## 6. The Agda code

### `flip` and `max-var`

```agda
flip : Literal → Literal
flip (pos n) = neg n
flip (neg n) = pos n

max-var : NNF → ℕ
max-var (lit (pos n)) = n
max-var (lit (neg n)) = n
max-var (a ∧n b)      = max-var a ⊔ max-var b
max-var (a ∨n b)      = max-var a ⊔ max-var b
```

`flip` negates a literal (we can't prefix `¬` syntactically on
`Literal`). `suc (max-var φ)` is guaranteed fresh — strictly greater
than every variable in φ.

### List builders for non-empty `Disjunct`/`CNF`

```agda
disjunct-of : Literal → List Literal → Disjunct
disjunct-of ℓ []        = lit ℓ
disjunct-of ℓ (m ∷ ms)  = ℓ ∨d disjunct-of m ms

cnf-of : Disjunct → List Disjunct → CNF
cnf-of d []        = dis d
cnf-of d (e ∷ es)  = d ∧c cnf-of e es
```

Pure plumbing: take a non-empty list (split into head + tail) and
build the right-nested cons-list. Since `Disjunct`/`CNF` are non-empty
(note 03), we can't `foldr` over a possibly-empty list.

### The workhorse: `tseytin-aux`

```agda
tseytin-aux : ℕ → NNF → ℕ × Literal × List Disjunct
```

Given a next-fresh index `n` and an NNF `φ`, return `(n', top, cs)`:

- `n'` — new next-fresh, ≥ every used variable + 1.
- `top` — literal representing the value of `φ` (either an original
  literal or `pos x` for some fresh `x`).
- `cs` — clauses generated.

**Literal case** — no fresh variable, no clauses:

```agda
tseytin-aux n (lit ℓ) = n , ℓ , []
```

Optimisation from §3: don't waste a fresh variable on something
already a literal.

**Conjunction case** — recurse on both children (threading `n`),
allocate `x`, emit the three iff-clauses:

```agda
tseytin-aux n (a ∧n b) with tseytin-aux n a
... | n₁ , la , cs₁ with tseytin-aux n₁ b
...   | n₂ , lb , cs₂ =
            let x   = n₂
                n₃  = suc n₂
                c₁ = disjunct-of (neg x) (la ∷ [])           -- ¬x ∨ la
                c₂ = disjunct-of (neg x) (lb ∷ [])           -- ¬x ∨ lb
                c₃ = disjunct-of (flip la) (flip lb ∷ pos x ∷ [])
                                                              -- ¬la ∨ ¬lb ∨ x
            in n₃ , pos x , c₁ ∷ c₂ ∷ c₃ ∷ cs₁ ++ cs₂
```

Crucial detail: passing `n₁` (not `n`) to the second recursive call
keeps `b`'s fresh variables disjoint from `a`'s. The disjunction case
is identical in shape with the three `∨` clauses from §4.

### Top-level

```agda
tseytin : NNF → CNF
tseytin φ with tseytin-aux (suc (max-var φ)) φ
... | _ , top , cs = cnf-of (lit top) cs
```

Start fresh-counter at `suc (max-var φ)` so no fresh variable clashes
with an original one. Prepend the unit clause `top` asserting "the
top representative is true", which by construction means "φ is true".

## 7. Equisatisfiability, sketch

**From a model of φ to a model of `tseytin φ`.** Given ρ that
satisfies φ, extend it by setting each fresh `x_ψ := eval-nnf ρ ψ`.
Every iff-clause is satisfied by construction; the top unit clause
holds because `eval-nnf ρ φ = true`.

**From a model of `tseytin φ` to a model of φ.** Given σ satisfying
`tseytin φ`, restrict to original variables to get ρ. By induction on
ψ, the iff-clauses force `σ(x_ψ) = eval-nnf ρ ψ`. The top unit
clause forces `σ(x_root) = true`, so `eval-nnf ρ φ = true`.

So φ is satisfiable iff `tseytin φ` is.

## 8. The complete pipeline

For any `Formula φ`:

1. `to-nnf φ` (note 02) — equivalence-preserving, linear.
2. `tseytin (to-nnf φ)` (this note) — equisatisfiability-preserving,
   linear.
3. `sat? (tseytin (to-nnf φ))` (note 05) — sound and complete DPLL.

The composition decides satisfiability of any propositional formula.
Tseytin is the link that makes the chain practical instead of
exponential.
