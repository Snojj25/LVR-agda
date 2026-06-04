# Note 11 — Problem 11: NNF → CNF (Tseytin Transformation)

Problem 11: convert an NNF formula to an **equisatisfiable** CNF.
Code: `src/Solution.agda`, Problem 11 section. Interactive
visualisation: [problem11-visual.html](problem11-visual.html)
(step-by-step over the NNF tree). This completes the pipeline

```
Formula  →[Problem 3]→  NNF  →[Problem 11]→  CNF  →[Problem 9]→  SAT/UNSAT
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

So *equivalence-preserving* CNF conversion can be exponential. To stay
linear, we have to weaken what "preserves the formula" means.

## 2. Equivalence vs equisatisfiability

- φ and ψ are **equivalent** if `eval ρ φ = eval ρ ψ` for every ρ —
  same set of models.
- φ and ψ are **equisatisfiable** if "φ has a model ⟺ ψ has one".
  Much weaker; ψ may use fresh variables and have very different
  models.

For SAT we only ask "is there *some* model?", so equisatisfiability
is exactly enough — and Tseytin delivers it at linear size. (This is
why the problem says "equisatisfiable", not "equivalent".)

## 3. The idea

For every **internal node** of the NNF tree, introduce one fresh
variable `x` that *names* the value of that subformula, and emit
clauses encoding the biconditional

```
x ↔ (la ∧ lb)        (for an ∧-node, children named la, lb)
x ↔ (la ∨ lb)        (for an ∨-node)
```

Leaves (literals) need no fresh variable — the literal already names
its own value. Finally, one unit clause asserts the root's name is
true.

No blow-up: subformulas are never duplicated — each gets *one* name
that other clauses refer to. Each node yields exactly 3 constant-size
clauses, so the CNF has ≤ `3·n + 1` clauses for `n` NNF nodes — `O(n)`
versus the `2ⁿ` of naive distribution.

## 4. Encoding `↔` as clauses

Using `a → b ≡ ¬a ∨ b`:

| `x ↔ (la ∧ lb)`   |  meaning           | `x ↔ (la ∨ lb)`   |  meaning      |
| ------------------ | ------------------ | ------------------ | ------------- |
| `¬x ∨ la`          | x → la             | `¬x ∨ la ∨ lb`     | x → la ∨ lb   |
| `¬x ∨ lb`          | x → lb             | `¬la ∨ x`          | la → x        |
| `¬la ∨ ¬lb ∨ x`    | la ∧ lb → x        | `¬lb ∨ x`          | lb → x        |

Three clauses per node in both cases.

## 5. The code

### Helpers

```agda
flip-lit : Literal → Literal        -- pos n ↔ neg n
flip-lit (pos n) = neg n
flip-lit (neg n) = pos n

max-var : NNF → ℕ                   -- largest variable index in φ
max-var (lit ℓ)   = max-var-lit ℓ
max-var (a ∧n b)  = max-var a ⊔ max-var b
max-var (a ∨n b)  = max-var a ⊔ max-var b

clauses-to-cnf : Disjunct → List Disjunct → CNF
clauses-to-cnf d []        = dis d
clauses-to-cnf d (c ∷ cs)  = d ∧c clauses-to-cnf c cs
```

`flip-lit` builds the `¬la` literals for the clause tables above (we
cannot syntactically prefix `¬` onto a `Literal`). `suc (max-var φ)`
is guaranteed fresh — strictly greater than every variable in φ.
`clauses-to-cnf` folds a head clause plus a list of clauses into the
non-empty `CNF` type (a plain `foldr` will not do, because `CNF` has
no empty case — the explicit head guarantees non-emptiness).

### The workhorse

```agda
tseytin : NNF → ℕ → ℕ × Literal × List Disjunct
```

Given a formula and the next free variable index `n`, return
`(n′ , l , cs)`:

- `n′` — updated next-free index (threaded through the recursion),
- `l` — the literal *naming* this subformula (an original literal for
  a leaf, `pos x` with `x` fresh for an internal node),
- `cs` — the clauses generated for this subtree.

```agda
tseytin (lit ℓ)  n = n , ℓ , []          -- leaf: no fresh var, no clauses
tseytin (a ∧n b) n with tseytin a n
... | n₁ , la , cs-a with tseytin b n₁
...   | n₂ , lb , cs-b =
        suc n₂ , pos n₂ ,
          (neg n₂ ∨d lit la)                            -- ¬x ∨ la
        ∷ (neg n₂ ∨d lit lb)                            -- ¬x ∨ lb
        ∷ (flip-lit la ∨d flip-lit lb ∨d lit (pos n₂))  -- ¬la ∨ ¬lb ∨ x
        ∷ (cs-a ++ cs-b)
```

(the `∨n` case is identical in shape, with the three `∨`-clauses from
§4). The crucial detail: the second recursive call receives `n₁`, the
index returned by the first — this keeps `b`'s fresh variables
disjoint from `a`'s.

### Top level

```agda
to-cnf : NNF → CNF
to-cnf φ with tseytin φ (suc (max-var φ))
... | _ , root , cs = clauses-to-cnf (lit root) cs
```

- The counter starts at `suc (max-var φ)`, above every original
  variable — **no collisions**.
- The first clause is the unit clause `root`, asserting "the name of
  the whole formula is true".
- For a bare literal `lit ℓ` the clause list is empty and the result
  is just `dis (lit ℓ)` — already CNF.

## 6. Worked example

Input NNF: `lit (pos 0) ∧n lit (pos 1)` (i.e. `x₀ ∧ x₁`), with
`max-var = 1`, so fresh variables start at 2.

1. Left leaf → `(2 , pos 0 , [])`; right leaf → `(2 , pos 1 , [])`.
2. The `∧`-node allocates `x₂` and returns `(3 , pos 2 , clauses)`.
3. `to-cnf` prepends the root unit clause:

```
x₂ ∧ (¬x₂ ∨ x₀) ∧ (¬x₂ ∨ x₁) ∧ (¬x₀ ∨ ¬x₁ ∨ x₂)
```

A model must set `x₂ = true`, which forces `x₀ = x₁ = true` — exactly
the models of the input (plus the bookkeeping variable).

## 7. Equisatisfiability, sketched

**(⇒)** From a model ρ of φ, extend it by `x_ψ ≔ eval-nnf ρ ψ` for
every internal node ψ. All biconditional clauses hold by construction,
and the root unit clause holds because `eval-nnf ρ φ = just true`.

**(⇐)** From a model σ of `to-cnf φ`: the biconditional clauses force
`σ(x_ψ)` to equal the value of ψ under σ, by induction from leaves
upward; the root unit clause forces that value to be `true` for the
whole formula. Restricting σ to the original variables gives a model
of φ.

A formal Agda proof of this would need structural induction with
clause-level lemmas — explicitly out of the project's scope (the note
in the handout accepts this; see also how Problem 12 *sidesteps* the
need for this theorem). What our tests do check
(`src/Tests.agda`, Problem 11 section) is that `sat? (to-cnf ψ)`
agrees with satisfiability of ψ on concrete examples.

## 8. Relation to Problem 12

Problem 12 calls `to-cnf (to-nnf φ)` and runs the Problem 9 solver on
the result. Without Tseytin, the CNF could be exponentially larger
than φ; with it, the whole pipeline stays linear in formula size
(modulo the exponential worst case of SAT search itself).
