# Note 01 — Propositional Formulas as an Inductive Type

Problem 1: define `Formula` in Agda. Code: `src/Solution.agda` lines
40–48. Every later problem reduces to recursion on these four
constructors.

## 1. Propositional logic in one paragraph

Atoms (propositional variables) are black boxes that are true or
false. Compound formulas are built with `¬`, `∧`, `∨`, `→`, `↔`. We
keep only `¬`, `∧`, `∨` because the rest are definable:

```
φ → ψ   ≡   ¬φ ∨ ψ
φ ↔ ψ   ≡   (¬φ ∨ ψ) ∧ (¬ψ ∨ φ)
```

`{¬, ∧, ∨}` is functionally complete, so we lose no expressive power.

## 2. Formulas as trees

A formula is a tree. `(p ∨ q) ∧ ¬r` is

```
        ∧
       / \
      ∨   ¬
     / \   \
    p   q   r
```

The string is the *concrete syntax*; the tree is the *abstract
syntax*. As a grammar:

```
Formula  ::=  Var n  |  ¬ Formula  |  Formula ∧ Formula  |  Formula ∨ Formula
```

In Agda (`src/Solution.agda` lines 40–44):

```agda
data Formula : Set where
  var  : ℕ → Formula
  ¬f_  : Formula → Formula
  _∧f_ : Formula → Formula → Formula
  _∨f_ : Formula → Formula → Formula
```

One constructor per grammar clause.

## 3. Why ℕ for variable names?

Two practical reasons:

1. **Decidable equality.** `_≟_ : (m n : ℕ) → Dec (m ≡ n)` from the
   stdlib — needed for assignment lookup and the SAT solver.
2. **Fresh variables.** The Tseytin transformation invents new
   variables: `suc (max-var φ)` is a one-liner on `ℕ`.

`var n` just means "variable named `n`". Strings would also work but
cost more.

## 4. The `f` suffix on constructors

`Data.Bool` already exports `_∧_` and `_∨_` (functions on `Bool`). If
our `Formula` constructors used those names, the same file would have
two operators sharing a spelling — particularly confusing in `eval`,
which pattern-matches on one and returns the other. The suffix tags
the type: `∧f` for `Formula`, `∧n` for `NNF`, `∧c` for `CNF`. The
Bool operators are renamed `and` / `or` at the import site
(`Solution.agda` lines 17–19).

## 5. Fixity declarations

```agda
infix  9 ¬f_
infixr 7 _∧f_
infixr 6 _∨f_
```

- **Precedence** (the number): higher binds tighter. So `¬f a ∧f b` is
  `(¬f a) ∧f b`, and `a ∧f b ∨f c` is `(a ∧f b) ∨f c`.
- **Associativity**: `infixr` is right-associative, so
  `a ∧f b ∧f c` is `a ∧f (b ∧f c)`.

The ordering `¬ > ∧ > ∨` matches textbook convention: `¬p ∧ q ∨ r`
parses as `((¬p) ∧ q) ∨ r`.

## 6. Examples

```agda
example₁ : Formula
example₁ = var 0 ∧f (var 1 ∨f var 2)

example₂ : Formula
example₂ = ¬f (var 0 ∧f var 1) ∨f var 2
```

In `example₁` the inner parentheses are *necessary*: without them
`∧f` binds tighter, giving a different tree with different meaning.

## 7. The induction principle

By giving Agda these four clauses (and no others), every function on
`Formula` is defined by four cases:

```agda
f : Formula → A
f (var n)    = …
f (¬f φ)     = … (f φ) …
f (a ∧f b)   = … (f a) … (f b) …
f (a ∨f b)   = … (f a) … (f b) …
```

Termination is automatic: each recursive call moves to a strictly
smaller sub-tree. Every later function on `Formula` (`to-nnf`, `eval`,
…) follows this template.

## 8. Deep vs shallow embedding

Our `Formula` is a *deep* embedding: formulas are *values* you can
pattern-match on, traverse, and transform. The alternative — a
*shallow* embedding identifying `p ∧ q` with the host's `P × Q` —
makes syntactic manipulation impossible. Since Problems 2–10 are
exactly about transforming syntax (to NNF, CNF, with fresh variables),
deep is the only sensible choice; the price is writing `eval`
explicitly to recover meaning.
