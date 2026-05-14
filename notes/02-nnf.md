# Note 02 — Negation Normal Form

Problems 2 and 3: the `Literal` and `NNF` datatypes, and
`to-nnf : Formula → NNF`. Code: `src/Solution.agda` lines 58–99.

## 1. What is NNF?

A formula is in **Negation Normal Form** when negation appears *only*
directly in front of a variable. No `¬(a ∧ b)`, no `¬(a ∨ b)`, no
`¬¬φ`.

```
Literal  ℓ ::=  Var n  |  ¬ Var n
NNF      ψ ::=  ℓ  |  ψ ∧ ψ  |  ψ ∨ ψ
```

Key restriction: at the NNF level there is **no negation
constructor**. The only `¬` lives inside a literal.

## 2. Why NNF?

- **Launching pad for CNF/DNF.** Both are sub-grammars of NNF.
- **Tseytin (Problem 10) needs NNF input.** No polarity reasoning per
  node — three node shapes only.
- **Fewer cases.** Functions over `NNF` have three cases (`lit`,
  `∧n`, `∨n`) instead of four.
- **Polarity is explicit.** Each occurrence carries `pos n` or `neg n`.

## 3. `Literal`

```agda
data Literal : Set where
  pos : ℕ → Literal     -- the literal  Var n
  neg : ℕ → Literal     -- the literal  ¬ Var n
```

A tagged variable index. The invariant "¬ wraps a variable only" is
structural — there is no constructor that could violate it. We make
bad values *unrepresentable* rather than ruling them out by predicate.

A small helper used in Tseytin:

```agda
flip : Literal → Literal
flip (pos n) = neg n
flip (neg n) = pos n
```

## 4. `NNF`

```agda
data NNF : Set where
  lit  : Literal → NNF
  _∧n_ : NNF → NNF → NNF
  _∨n_ : NNF → NNF → NNF
```

Mirror of `Formula` with two changes: leaves are literals (carrying
polarity), and there is no negation constructor.

## 5. The conversion: pushing `¬` to the leaves

The textbook algorithm rewrites φ repeatedly using four laws until
every `¬` sits on a variable:

```
¬(a ∧ b) ≡ ¬a ∨ ¬b       (De Morgan, ∧)
¬(a ∨ b) ≡ ¬a ∧ ¬b       (De Morgan, ∨)
¬¬ φ     ≡ φ             (double-negation elimination)
¬(Var n) ≡ neg n         (base case: ¬ is absorbed into a literal)
```

Intuition: think of `¬` as a token that wants to *travel to a leaf*.
At an `∧` or `∨`, De Morgan dives it past the connective, flipping
`∧ ↔ ∨` and *duplicating* itself to negate each child. At another
`¬`, the two cancel. At a `Var n`, it disappears into the polarity
tag `neg n`. Non-negated `∧`, `∨`, `Var` just recurse.

So the *specification* is "iterate the four rules to a fixed point".
The *implementation* problem is to encode this as a structurally
recursive Agda function the termination checker will accept.

### The naive attempt fails termination

The most direct translation of the rules is one equation per case:

```agda
to-nnf : Formula → NNF
to-nnf (var n)            = lit (pos n)
to-nnf (¬f var n)         = lit (neg n)
to-nnf (¬f ¬f φ)          = to-nnf φ
to-nnf (¬f (a ∧f b))      = to-nnf (¬f a ∨f ¬f b)   -- De Morgan
to-nnf (¬f (a ∨f b))      = to-nnf (¬f a ∧f ¬f b)   -- De Morgan
to-nnf (a ∧f b)           = to-nnf a ∧n to-nnf b
to-nnf (a ∨f b)           = to-nnf a ∨n to-nnf b
```

Semantically perfect. But Agda rejects it on the De Morgan cases:

```agda
to-nnf (¬f (a ∧f b)) = to-nnf (¬f a ∨f ¬f b)
```

Agda's termination checker is **structural**: a recursive call is
accepted only if its argument is a strict sub-term of the input —
literally something obtained by stripping constructors. The
argument `¬f a ∨f ¬f b` is *not* such a sub-term of `¬f (a ∧f b)`:

- we kept `a` and `b` (which *are* sub-terms),
- but we wrapped each in a fresh `¬f`,
- and replaced the outer `∧f` with a fresh `∨f`.

By constructor count it is no smaller — in fact it has *more*
constructors than the input. Agda gives up. (The function *does*
terminate, but proving it requires a custom well-founded measure on
formulas — doable but heavy machinery.)

### Fix: two mutually recursive helpers

Define **two** functions instead of one. The trick is to make
"applying `¬` to the next call" a choice between *which function*
we call, rather than something we build with constructors.

```agda
nnf⁺ : Formula → NNF
nnf⁻ : Formula → NNF

nnf⁺ (var n)   = lit (pos n)
nnf⁺ (¬f φ)    = nnf⁻ φ
nnf⁺ (a ∧f b)  = nnf⁺ a ∧n nnf⁺ b
nnf⁺ (a ∨f b)  = nnf⁺ a ∨n nnf⁺ b

nnf⁻ (var n)   = lit (neg n)
nnf⁻ (¬f φ)    = nnf⁺ φ                 -- ¬¬φ ≡ φ
nnf⁻ (a ∧f b)  = nnf⁻ a ∨n nnf⁻ b       -- ¬(a∧b) ≡ ¬a ∨ ¬b
nnf⁻ (a ∨f b)  = nnf⁻ a ∧n nnf⁻ b       -- ¬(a∨b) ≡ ¬a ∧ ¬b

to-nnf : Formula → NNF
to-nnf = nnf⁺
```

The specifications (what each function *means*):

- **`nnf⁺ φ`** produces an NNF equivalent to `φ` — "translate φ
  under positive polarity".
- **`nnf⁻ φ`** produces an NNF equivalent to `¬ φ` — "translate the
  *negation* of φ, without ever building `¬f φ` syntactically".

So `nnf⁻` is *not* "the negation of `nnf⁺`'s result". It is what
`nnf⁺` would have produced if we'd handed it `¬f φ` — computed
directly, in one pass. The four equations of `nnf⁻` literally encode
the four De Morgan / double-negation rewrites, but the rewrites
happen on the *function we call*, not on the syntax we build:

| pattern         | rule used                | what `nnf⁻` does           |
| --------------- | ------------------------ | -------------------------- |
| `nnf⁻ (var n)`  | `¬(Var n) ≡ neg n`       | emit `lit (neg n)`         |
| `nnf⁻ (¬f φ)`   | `¬¬φ ≡ φ`                | call `nnf⁺ φ`              |
| `nnf⁻ (a ∧f b)` | `¬(a∧b) ≡ ¬a ∨ ¬b`       | `nnf⁻ a ∨n nnf⁻ b`         |
| `nnf⁻ (a ∨f b)` | `¬(a∨b) ≡ ¬a ∧ ¬b`       | `nnf⁻ a ∧n nnf⁻ b`         |

The two-function shape *exactly mirrors the parity of `¬`s*: an even
number of negations seen so far ⇒ we are inside `nnf⁺`; an odd
number ⇒ we are inside `nnf⁻`. Crossing a `¬f` flips the parity
(swaps which function we are in). `to-nnf` enters at `nnf⁺` —
parity zero — and we never need to remember a count.

### Why this passes the termination checker

Every recursive call now passes a *strict sub-term* of the input:

| caller          | recursive argument | strict sub-term of input? |
| --------------- | ------------------ | ------------------------- |
| `nnf⁺ (¬f φ)`   | `φ`                | yes (strip `¬f`)          |
| `nnf⁺ (a ∧f b)` | `a`, `b`           | yes (strip `∧f`)          |
| `nnf⁺ (a ∨f b)` | `a`, `b`           | yes (strip `∨f`)          |
| `nnf⁻ (¬f φ)`   | `φ`                | yes                       |
| `nnf⁻ (a ∧f b)` | `a`, `b`           | yes                       |
| `nnf⁻ (a ∨f b)` | `a`, `b`           | yes                       |

No fresh `¬f` ever appears in a recursive argument — the "flip" we
used to do by building syntax (`¬f a ∨f ¬f b`) is now done at the
*meta level* by switching from `nnf⁺` to `nnf⁻`. Termination is
accepted without any well-founded recursion machinery.

### `to-nnf` as a one-liner

```agda
to-nnf : Formula → NNF
to-nnf = nnf⁺
```

By specification `nnf⁺ φ` is already "an NNF equivalent to φ" —
exactly what `to-nnf` should produce. `nnf⁻` is purely an internal
helper, never called from outside.

**General idiom**: when a logical rewrite would build new syntax that
breaks Agda's structural termination check, encode the rewrite as a
choice between mutually recursive functions over the *original*
syntax. Polarity-tracking functions (`nnf⁺` / `nnf⁻`) are the
canonical instance; the same trick appears whenever you'd otherwise
need to apply a transformation "on the way down" a recursion.

## 6. Worked example

Let `p ≔ var 0`, `q ≔ var 1`, `r ≔ var 2`, and
`φ = ¬f ((p ∨f ¬f q) ∧f r)`. Tracing `nnf⁺ φ`:

```
nnf⁺ (¬f ((p ∨f ¬f q) ∧f r))
=  nnf⁻ ((p ∨f ¬f q) ∧f r)               -- nnf⁺ on ¬f
=  nnf⁻ (p ∨f ¬f q) ∨n nnf⁻ r            -- ¬(a∧b)
=  (nnf⁻ p ∧n nnf⁻ (¬f q)) ∨n nnf⁻ r     -- ¬(a∨b)
=  (nnf⁻ p ∧n nnf⁺ q) ∨n nnf⁻ r          -- ¬¬φ
=  (lit (neg 0) ∧n lit (pos 1)) ∨n lit (neg 2)
```

i.e. `(¬p ∧ q) ∨ ¬r`.

## 7. Correctness, informally

For every `ρ` and `φ`,

```
eval ρ φ       ≡ eval-nnf ρ (nnf⁺ φ)         (S⁺)
eval ρ (¬f φ)  ≡ eval-nnf ρ (nnf⁻ φ)         (S⁻)
```

These imply `eval ρ φ ≡ eval-nnf ρ (to-nnf φ)`. Proof by mutual
structural induction on `φ`, one case per equation. The `_∧f_` case
of (S⁻) uses Boolean De Morgan: `not (x and y) ≡ not x or not y`.
Writing the proof in Agda is a worthwhile exercise but not part of
the project.

## 8. Where this leads

NNF is the common ancestor of two stricter normal forms:

- **CNF** (note 03): conjunction of disjunctions of literals.
- **DNF**: the dual.

The pipeline `Formula → NNF → CNF` continues in note 03 (CNF type)
and note 06 (Tseytin: an NNF to *equisatisfiable* CNF in linear size).
