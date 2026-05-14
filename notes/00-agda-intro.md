# Note 00 — A Short Introduction to Agda

Enough Agda to read `src/Solution.agda` and follow the other notes.

## 1. What is Agda?

Agda is a *dependently typed* functional language. Two views:

1. **Programming language**: like Haskell — pure, functional, ADTs,
   pattern matching.
2. **Proof assistant**: types can encode mathematical statements, and
   programs are their proofs. If your program type-checks, the theorem
   holds. (Curry–Howard.)

## 2. Types

Types are first-class values and may depend on other values.

- `ℕ` — naturals (`zero`, `1`, `2`, …).
- `Bool` — booleans.
- `List ℕ` — lists of naturals.
- `Vec ℕ 3` — lists of naturals **of length exactly 3** (the `3` is
  part of the type — dependent typing).

Because types talk about values, the type checker rules out many bugs.

## 3. Syntax

- Whitespace-sensitive layout.
- Unicode is everywhere: `→`, `∀`, `≡`, `ℕ`, … Type `\to`, `\bN`, `\==`
  in editor mode.
- Underscores in a name mark **argument positions** for mixfix
  operators: `_+_` is `2 + 3`; `if_then_else_` is `if b then x else y`.

A file starts with a module declaration:

```agda
module HelloAgda where
```

## 4. Data types

Declare a data type by its **constructors**:

```agda
data Bool : Set where
  true  : Bool
  false : Bool

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
```

So `2` is `suc (suc zero)`. `Set` means "this is a type".

## 5. Functions and pattern matching

```agda
not : Bool → Bool
not true  = false
not false = true

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)
```

Pattern matching is exhaustive and functions must be **total** (the
termination checker rejects unbounded recursion).

## 6. Polymorphism

Curly braces mark *implicit* arguments — Agda infers them:

```agda
id : ∀ {A : Set} → A → A
id x = x
```

Call as `id 5`; `{A}` is inferred.

## 7. Propositions as types

The empty type is "false":

```agda
data ⊥ : Set where  -- no constructors
```

Equality is a type with constructor `refl`:

```agda
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
```

A *proof* of `2 + 2 ≡ 4` is just a value of that type.

## 8. Where to go next

The notes that follow define `Formula` (note 01), recursive functions
over it (notes 02–03), and the surrounding machinery. For deeper
study: Wadler's *Programming Language Foundations in Agda* (PLFA),
free online.
