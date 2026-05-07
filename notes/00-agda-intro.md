# Note 00 — A Short Introduction to Agda

A minimal first look at Agda — enough to read this project's code
(`src/Solution.agda`) and follow the other notes.

## 1. What is Agda?

Agda is a *dependently typed* functional programming language. Two ways
to think about it:

1. As a **programming language**: similar to Haskell — pure, functional,
   with algebraic data types and pattern matching.
2. As a **proof assistant**: its type system is expressive enough that
   *types can encode mathematical statements* and *programs can be
   their proofs*. If your program type-checks, the theorem holds.

"Writing a proof" and "writing a function whose type is the statement"
are literally the same thing — Curry–Howard in practice.

## 2. The big idea: types

In most languages a type is a tag (`int`, `string`, `List<User>`). In
Agda, types are *first-class values* and can depend on other values.

- `ℕ` is the type of natural numbers (`zero`, `1`, `2`, …).
- `Bool` is the type of booleans (`true`, `false`).
- `List ℕ` is the type of lists of naturals.
- `Vec ℕ 3` is the type of lists of naturals **of length exactly 3**.
  The number `3` *is part of the type* — that is a dependent type.

Because types can talk about values, the type-checker rules out a huge
class of bugs: indexing past the end of a vector, missing cases,
returning the wrong shape of data.

## 3. Basic syntax

- Agda is **whitespace-sensitive** for layout (like Haskell or Python),
  with lenient indentation rules.
- It uses lots of **Unicode**: `→`, `∀`, `∃`, `≡`, `ℕ`, `⊥`, `⊤`, …
  In Agda mode (Emacs/VSCode) you type `\to` for `→`, `\bN` for `ℕ`,
  `\==` for `≡`, etc.
- Identifiers can be almost anything: `x`, `n+1`, `_∧_`, `is-even?`.
- Underscores in a name mark **argument positions** for mixfix
  operators: `_+_` is used as `2 + 3`; `if_then_else_` as
  `if b then x else y`.

A file usually starts with a module declaration:

```agda
module HelloAgda where
```

## 4. Data types

Declare a data type by listing its **constructors**:

```agda
data Bool : Set where
  true  : Bool
  false : Bool

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
```

Read: "`Bool` is a `Set` (a type), with two ways to build one." A
natural is either `zero` or `suc n` for some smaller `ℕ` (so `2` is
`suc (suc zero)`).

`Set` is Agda's name for "the type of ordinary types"; treat `: Set` as
"this is a type".

## 5. Functions and pattern matching

Functions have a **type signature** and one or more **equations**:

```agda
not : Bool → Bool
not true  = false
not false = true

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)
```

- `→` is the function arrow. `ℕ → ℕ → ℕ` means "take a `ℕ`, then
  another `ℕ`, return a `ℕ`".
- Pattern matching is exhaustive — Agda complains about missing cases
  and refuses functions that might loop forever. Functions are *total*.

## 6. Generic (polymorphic) functions

Type parameters use `∀` or curly braces. Curly braces are *implicit* —
Agda infers them from context:

```agda
id : ∀ {A : Set} → A → A
id x = x

length : ∀ {A : Set} → List A → ℕ
length []        = zero
length (x ∷ xs)  = suc (length xs)
```

Call them as `id 5` or `length (1 ∷ 2 ∷ [])`; `{A}` is inferred.

## 7. Propositions as types (a tiny taste)

Some types have *no* values. The empty type is the proposition "false":

```agda
data ⊥ : Set where  -- no constructors
```

Negation is "if you give me a proof of `P`, I give you a proof of
false":

```agda
¬_ : Set → Set
¬ P = P → ⊥
```

Equality is itself a type, with one constructor `refl` (reflexivity):

```agda
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
```

A *proof* that `2 + 2 ≡ 4` is just a value of type `2 + 2 ≡ 4` — and
writing it is writing a small program. This is the bridge between code
and math that makes Agda special.

## 8. How Agda is used in practice

The workflow is interactive. Write a function with a hole:

```agda
double : ℕ → ℕ
double n = ?
```

In an editor with Agda mode you can:

- Ask Agda the **type** of the hole (`C-c C-,`).
- **Case-split** on a variable (`C-c C-c`).
- **Refine** the hole with a partial term (`C-c C-r`).
- Let Agda **solve** simple goals automatically (`C-c C-a`).

You converse with the type-checker: it reports what's missing, you
fill in a piece, it reports what's left. When there are no holes and
the file type-checks, you're done — as both programmer and
mathematician.

## 9. Where to go next

That's enough for this project. The following notes build on this
vocabulary: an inductive `Formula` type (note 01), recursive functions
over it (notes 02–03), and proofs by induction (later notes).

Once you want more:

- Philip Wadler's *Programming Language Foundations in Agda* (PLFA) —
  free online, the standard gentle introduction.
- The Agda standard library (`agda-stdlib`) — read `Data.Nat`,
  `Data.List`, `Relation.Binary.PropositionalEquality`.
- Experiment in the editor; Agda is much easier *with* interactive mode.
