# Note 01 — Propositional Formulas as an Inductive Type

This note unpacks Problem 1 of the project: defining the type `Formula`
of propositional logic formulas in Agda. The corresponding code lives
in `src/Solution.agda`, lines 38–48. Every later problem (NNF in note
02, evaluation in note 03, assignments in note 04, CNF and SAT later)
reduces to recursion on the four constructors introduced here.

The piece of code we are explaining is nine lines, but those nine
lines fix precisely *what kind of mathematical object* we will study
for the rest of the project.

## 1. What is propositional logic?

Propositional logic is the logic of *atomic* statements glued together
by Boolean connectives. Each atom — a "propositional variable", or
just "variable" — is a black box that is either *true* or *false*. We
do not look inside; for propositional logic, an atom is just a name.

Out of atoms we build *compound* formulas using connectives:

- Negation `¬φ`, read "not φ".
- Conjunction `φ ∧ ψ`, read "φ and ψ".
- Disjunction `φ ∨ ψ`, read "φ or ψ" (inclusive).
- Implication `φ → ψ`, read "if φ then ψ".
- Biconditional `φ ↔ ψ`, read "φ if and only if ψ".

We only put `¬`, `∧`, `∨` into our datatype, because `→` and `↔` are
*redundant*. Any formula using them can be rewritten:

```
φ → ψ   ≡   ¬φ ∨ ψ
φ ↔ ψ   ≡   (φ → ψ) ∧ (ψ → φ)   ≡   (¬φ ∨ ψ) ∧ (¬ψ ∨ φ)
```

The first is "material implication"; the second unfolds `↔` as two
implications joined by `∧`. Keeping the core type small means once we
have written `eval`, `to-nnf`, etc. for `{¬, ∧, ∨}`, we have
implicitly handled `{→, ↔}` too: just desugar before you start.

The set `{¬, ∧, ∨}` is also *functionally complete* for two-valued
semantics — every Boolean function `Bool^n → Bool` can be expressed
using these connectives alone, so we lose no expressive power.

## 2. Abstract syntax: formulas as trees

A formula is fundamentally a *tree*. The formula

```
(p ∨ q) ∧ ¬r
```

corresponds to the tree

```
        ∧
       / \
      ∨   ¬
     / \   \
    p   q   r
```

with atoms at the leaves and connectives at internal nodes. The string
`(p ∨ q) ∧ ¬r` is the *concrete syntax*; the tree is the *abstract
syntax*: the structured object the string denotes.

Logicians write the set of such trees with a grammar in Backus–Naur
Form (BNF):

```
Formula  ::=  Var n
           |  ¬ Formula
           |  Formula ∧ Formula
           |  Formula ∨ Formula
```

Read recursively: a formula is either a variable indexed by `n`, or
`¬φ`, `φ ∧ ψ`, or `φ ∨ ψ` for smaller formulas. Only finite trees are
formulas, because the grammar is generated *inductively* — every
formula is built from leaves up by finitely many rule applications.

Now look at the Agda definition (`src/Solution.agda` lines 40–44):

```agda
data Formula : Set where
  var  : ℕ → Formula
  ¬f_  : Formula → Formula
  _∧f_ : Formula → Formula → Formula
  _∨f_ : Formula → Formula → Formula
```

The `data` declaration is a *literal transcription* of the BNF
grammar, one constructor per clause:

- `var : ℕ → Formula`. Given `n`, `var n` is the atomic variable
  named `n`.
- `¬f_ : Formula → Formula`. Given `φ`, `¬f φ` represents `¬φ`.
- `_∧f_ : Formula → Formula → Formula`. `a ∧f b` is `a ∧ b`.
- `_∨f_ : Formula → Formula → Formula`. Likewise for disjunction.

The `: Set` part means `Formula` lives in Agda's universe of types,
alongside `ℕ` and `Bool`. This is a plain inductive type — the kind of
thing you would write as `enum Formula { Var(u32), Not(Box<Formula>),
And(Box<Formula>, Box<Formula>), Or(Box<Formula>, Box<Formula>) }` in
Rust, or a `sealed trait Formula` hierarchy in Scala. The Agda version
is more honest: "a `Formula` is *exactly* one of these four shapes,
and there is no other way to be a `Formula`".

## 3. Why ℕ for variable identifiers?

Variables are *just names*. We could have used strings, characters, or
any infinite type. We chose `ℕ` for two practical reasons:

1. **Decidable equality.** We need to compare variables for the
   assignment lookup (note 04) and the SAT solver. On `ℕ` we have
   `_≟_ : (m n : ℕ) → Dec (m ≡ n)` from the standard library; on
   strings we would need a heavier module.
2. **Fresh variable generation.** The Tseytin transformation in
   Problem 10 needs to invent variables not yet in the input. With
   `ℕ`, "one more than the current maximum" is a one-liner
   (`suc (max-var φ)` in `src/Solution.agda` line 357). With strings
   we would mangle names with primes or numeric suffixes and worry
   about collisions.

The choice of `ℕ` is *convenience*, not a fundamental commitment.
Anywhere you read `var n`, think "the variable whose name happens to
be the natural number `n`". `ℕ` is just the cleanest infinite,
decidably-equal, freshable name supply available.

## 4. Why `¬f_`, `_∧f_`, `_∨f_` instead of `¬_`, `_∧_`, `_∨_`?

Look at the comment in `src/Solution.agda` line 37–38:

> We use the constructors `var`, `¬f_`, `_∧f_`, `_∨f_` to avoid
> clashing with the homonymous operators on `Bool`.

The standard library's `Data.Bool` already exports:

```agda
_∧_ : Bool → Bool → Bool
_∨_ : Bool → Bool → Bool
```

These are *functions returning `Bool`*, not constructors of a syntax
type. If we named our `Formula` constructors `_∧_` and `_∨_`, the same
file would have two completely different operators with the same
spelling. Agda would tolerate this, but the result is confusing —
especially in `eval` (Problem 5), which pattern-matches on `Formula`
built with one operator and *returns* a `Bool` combined with the
other.

The convention in `Solution.agda` suffixes syntactic constructors with
a small letter hinting at the type:

| constructor | belongs to | reads as            |
| ----------- | ---------- | ------------------- |
| `¬f_`       | `Formula`  | "not, on a formula" |
| `_∧f_`      | `Formula`  | "and, on formulas"  |
| `_∨f_`      | `Formula`  | "or, on formulas"   |
| `_∧n_`      | `NNF`      | "and, on NNFs"      |
| `_∨n_`      | `NNF`      | "or, on NNFs"       |
| `_∧c_`      | `CNF`      | conjunction of CNF  |
| `_∨d_`      | `Disjunct` | within a disjunct   |
| `_and_`     | `Bool`     | renamed Bool ∧      |
| `_or_`      | `Bool`     | renamed Bool ∨      |

The renamings `_∧_ → _and_` and `_∨_ → _or_` happen at the import site
on lines 17–19 of `src/Solution.agda`, freeing up `_∧_` and `_∨_` so
the suffixed names visually still look like proper `∧` and `∨`. The
trailing letter is the tag, the wedge is the meaning.

## 5. Mixfix syntax and fixity declarations

Agda's identifier syntax is unusually permissive. An identifier may
contain almost any non-whitespace Unicode character, and `_` marks an
*argument hole* in a *mixfix* operator:

- `_∧f_` has two argument positions, used as `a ∧f b`.
- `¬f_` has one argument position after the symbol, used as `¬f φ`.
- `var` has no holes; called prefix-style as `var n`.

This lets the *constructors of the syntax tree* be written using the
*same notation as the logic itself*. No separate parser, no string
mangling — just four constructors with carefully placed underscores.

But mixfix alone is not enough. We must tell Agda how to parse
`a ∧f b ∨f c`: as `(a ∧f b) ∨f c` or `a ∧f (b ∨f c)`? And
`¬f a ∧f b` — `(¬f a) ∧f b` or `¬f (a ∧f b)`? The fixity declarations
on lines 46–48 answer that:

```agda
infix  9 ¬f_
infixr 7 _∧f_
infixr 6 _∨f_
```

Two pieces of information:

1. **Precedence (the number).** Higher binds tighter. So `¬f_` at 9
   binds tighter than `_∧f_` at 7, which binds tighter than `_∨f_` at
   6. Hence `¬f a ∧f b` is `(¬f a) ∧f b`, and `a ∧f b ∨f c` is
   `(a ∧f b) ∨f c`.

2. **Associativity (`infix` / `infixr` / `infixl`).** When the same
   operator appears repeatedly, which way does it associate? `infixr`
   is right-associative, so `a ∧f b ∧f c` parses as `a ∧f (b ∧f c)`.
   `infixl` would parse it as `(a ∧f b) ∧f c`. `infix` means "no
   default — parenthesise explicitly". `¬f_` is `infix` because it has
   only one argument, so the question doesn't arise.

The absolute precedence values do not matter; only the relative
ordering does. The chosen ordering — `¬` > `∧` > `∨` — matches the
standard mathematical convention: any textbook reads

```
¬p ∧ q ∨ r
```

as

```
((¬p) ∧ q) ∨ r
```

The numbers `6` and `7` were chosen to sit within the usual range of
the Agda standard library (arithmetic operators sit at 6–8). Any
choice with the right ordering is observationally equivalent here.

The right-associativity of `∧f` and `∨f` is a minor convenience: it
matches how we write iterated conjunctions and disjunctions, and the
recursive shape of `eval` and `to-nnf`. For commutative-associative
operators, the associativity choice has no semantic consequences — it
only affects tree shape, not meaning.

## 6. Some concrete examples

The constructors plus mixfix declarations let us write formulas in
essentially their textbook form:

```agda
example₁ : Formula
example₁ = var 0
-- AST:   var 0
```

```agda
example₂ : Formula
example₂ = ¬f var 0
-- AST:    ¬f
--          \
--          var 0
```

```agda
example₃ : Formula
example₃ = var 0 ∧f (var 1 ∨f var 2)
-- AST:        ∧f
--           /    \
--        var 0    ∨f
--                /  \
--             var 1  var 2
```

```agda
example₄ : Formula
example₄ = ¬f (var 0 ∧f var 1) ∨f var 2
-- AST:               ∨f
--                  /    \
--                ¬f      var 2
--                |
--               ∧f
--              /  \
--          var 0   var 1
```

In `example₃` the parentheses around `var 1 ∨f var 2` are *necessary*.
Without them, `var 0 ∧f var 1 ∨f var 2` parses as
`(var 0 ∧f var 1) ∨f var 2` since `∧f` binds tighter. That gives a
*different tree* with a *different meaning*: under
`0 → ⊥, 1 → ⊥, 2 → ⊤` we get `(⊥ ∧ ⊥) ∨ ⊤ = ⊤` versus
`⊥ ∧ (⊥ ∨ ⊤) = ⊥`. Parsing matters because *the tree is the meaning*,
and `eval` (Problem 5) walks the tree.

Note that `var 0`, `var 1`, `var 2` are syntactically distinct
formulas — different names — even before any assignment. They become
`Bool`s only when evaluated under an `Assignment` (note 04), which is
a function from variable names (`ℕ`) to truth values (`Bool`).

## 7. The induction principle

Here is the most important consequence of writing `data Formula` this
way. By giving Agda *all four* clauses and *no others*, we have told
it two things:

- **Introduction:** any formula can be built using these four
  constructors. This is what we use when we *write*
  `var 0 ∧f var 1`.
- **Elimination / induction:** any function out of `Formula` can be
  defined by four cases — one per constructor — and Agda's
  termination checker accepts the function as total provided
  recursive calls are made on *strictly smaller* sub-formulas.

To define `f : Formula → A` for any `A`:

```agda
f : Formula → A
f (var n)    = …                         -- base case
f (¬f φ)     = … (f φ) …                 -- recursive in φ
f (a ∧f b)   = … (f a) … (f b) …         -- recursive in a and b
f (a ∨f b)   = … (f a) … (f b) …         -- recursive in a and b
```

Termination is accepted because each recursive call goes from a parent
constructor to a constructor argument — the tree shrinks at every
step. Since every tree is finite, recursion always terminates.

Every function on `Formula` later in the project follows this
template:

- `to-nnf : Formula → NNF` (Problem 3) — see note 02. Its `nnf⁺` and
  `nnf⁻` mutually-recursive helpers in `src/Solution.agda` lines
  85–96 each have one equation per `Formula` constructor.
- `eval : Assignment → Formula → Maybe Bool` (Problem 5) in
  `src/Solution.agda` lines 147–157. Same four cases.
- `tseytin : NNF → CNF` (Problem 10), and the SAT solver in Problem 9,
  bottom out in similar four-case (or three-case, on `NNF`)
  recursions.

The same induction principle justifies *proofs* about formulas: to
prove `P : Formula → Set` for every formula, prove `P (var n)` for
every `n`, prove `P (¬f φ)` assuming `P φ`, and similarly for `∧f`,
`∨f`. We don't write such proofs in this project (Problems 1–10 are
about *executing* the syntax), but they would use exactly this
skeleton.

If you have seen structural induction on naturals — "prove `P 0`, then
`P (suc n)` assuming `P n`" — this is the same idea generalised to a
four-constructor tree. `ℕ` is a one-leaf, one-branch inductive type;
`Formula` is a one-leaf, three-branch (one unary, two binary) one.

## 8. Deep vs shallow embedding

A final framing point. There are two strategies for embedding a logic
into a host language like Agda:

- **Shallow embedding.** Identify object-language formulas with
  *propositions of the host*. `p ∧ q` is just the Agda type `P × Q`,
  or the Agda Boolean `b₁ and b₂`. There is no separate `Formula`
  type — the host language *is* the logic.
- **Deep embedding.** Define formulas as a *data type*, where each
  constructor is a piece of syntax. Formulas are *values* you can
  pattern-match on, traverse, print, transform. Their *meaning* is
  given separately by an interpreter (here, `eval`).

Our `Formula` is a deep embedding. That is what makes Problems 2–10
possible. We need to:

- transform formulas into other forms (NNF, CNF) — requires
  pattern-matching on structure, which a shallow embedding lacks;
- generate *fresh* variables in the Tseytin transformation — a
  shallow embedding has no notion of "the variables of a formula";
- count, traverse, hash, normalise, compare formulas — all syntactic.

The price is that we must write `eval` ourselves to recover *meaning*.
Shallow gives meaning for free but takes away syntactic manipulation.
For a project whose entire point is to transform syntax, deep is the
only sensible choice.

---

Where to next:

- Note 02 (`02-nnf.md`) introduces a *second* deep embedding, `NNF`,
  and the conversion `Formula → NNF`. Watch how the four-case
  induction principle becomes the engine of `to-nnf`.
- Note 04 (`04-assoc.md`) covers `Assignment`, the `ℕ → Bool` map
  giving `Formula` semantics — closing the loop between "formula as
  syntax" and "formula as truth value".
