# LVR Project — One‑File Guide

This single document explains every problem of the project, the design choices
in `src/Solution.agda`, and a short audit of Problems 5–8. It is written for
someone who is **coding this kind of task for the first time**, so it spends
extra time on the Agda mechanics that are easy to trip on.

If you only want to read one file, this is the one. The legacy per‑problem
notes (`01-formulas.md`, `02-nnf.md`, …) are now superseded and may be removed.

---

## 0. How to use this project

### 0.1 Verify everything

From the project root (`LVR-agda/`):

```sh
agda src/Solution.agda
```

A clean exit (no output errors) means **all ten problems type-check**.

### 0.2 The standard library

The project depends on `standard-library`. It is enough to register it once
in `~/.config/agda/libraries`, e.g.:

```
/usr/local/opt/agda/share/agda/stdlib/standard-library.agda-lib
```

(adjust to your Homebrew prefix). After that, `lvr-project.agda-lib` picks
it up automatically.

### 0.3 The two workflows

- **Terminal** (always works): edit → save → `agda src/Solution.agda` →
  fix errors → repeat.
- **Interactive** (Emacs `agda-mode` or a VS Code Agda extension): put `?`
  where you don’t know the term, "load" the file, refine each hole.

Either way the loop is the same: **edit → check → fix**.

---

## 1. The big picture

The project asks you to build, inside Agda, a small library for propositional
logic and CNF SAT solving:

1. an inductive **`Formula`** type for the grammar
   `Var n | ¬ φ | φ ∧ ψ | φ ∨ ψ`;
2. a **`NNF`** sub‑type (negation only at variables);
3. a function **`to-nnf`** translating `Formula → NNF`;
4. an **`Assoc`** module implementing a finite map
   `Var → Bool` (which we will call an "assignment");
5. a partial evaluator **`eval : Assignment → Formula → Maybe Bool`**;
6. the same for NNF (**`eval-nnf`**);
7. a **`CNF`** type;
8. a partial evaluator **`eval-cnf`** for CNF;
9. a **SAT solver** for CNF formulas;
10. an **equisatisfiable** translation **NNF → CNF** (Tseytin).

Problems 1–8 are routine type-theoretic encodings of the underlying maths.
9 and 10 are small algorithms on top of those types.

---

## 2. Agda crash course (the parts you actually need)

### 2.1 What `data ... where` does

```agda
data Formula : Set where
  var  : ℕ → Formula
  ¬f_  : Formula → Formula
  _∧f_ : Formula → Formula → Formula
  _∨f_ : Formula → Formula → Formula
```

This declares an **inductive datatype**. Each constructor builds a value of
`Formula` from smaller pieces. `Set` is Agda’s default universe of "ordinary
types".

The underscores in `¬f_`, `_∧f_`, `_∨f_` are **mixfix slots**: they tell Agda
to parse `a ∧f b` as the constructor `_∧f_ a b`. The leading `f` (and later
`n`, `d`, `c`) is just a tag to avoid clashing with the boolean operators
`_∧_` and `_∨_` from `Data.Bool` (we already renamed those to `_and_` and
`_or_`).

### 2.2 `infix` / `infixl` / `infixr`

```agda
infix  9 ¬f_
infixr 7 _∧f_
infixr 6 _∨f_
```

These don’t define anything new; they only tell the **parser** how to
disambiguate expressions:

- **Bigger number = binds tighter.** Here `¬f_` (9) binds tighter than
  `_∧f_` (7), which binds tighter than `_∨f_` (6). This matches the usual
  convention "¬ before ∧ before ∨".
- **`infixr`** = right‑associative: `a ∧f b ∧f c` parses as `a ∧f (b ∧f c)`.
- **`infixl`** = left‑associative.
- **`infix`** = non‑associative.

### 2.3 `Maybe` for partiality

`Maybe A = nothing | just a`. We use it to handle the fact that an
**assignment may not define every variable**. When evaluation runs into an
undefined variable, the whole formula evaluates to `nothing`.

### 2.4 `Dec A` for decidable predicates

`Dec A = yes (a : A) | no (¬ A)` — "we can decide whether `A` holds".
We use it for the decidable equality of natural numbers (`_≟_`), and to
decide membership in an associative list (`_∈?_`).

### 2.5 `with` clauses

```agda
eval ρ (¬f φ)    with eval ρ φ
... | just b  = just (not b)
... | nothing = nothing
```

`with e` lets you **pattern‑match on an intermediate expression** without
extracting it into a `let`. Every `...` line is a continuation of the same
clause; the bar separates the cases of `with`.

### 2.6 Termination

Agda only accepts functions whose recursion is **structurally decreasing**.
For us this means: always recurse on a sub‑term (a smaller `Formula`, a
shorter `List`, a smaller index). Every recursive function below does so
visibly, so Agda’s termination checker is happy.

---

## 3. Problem 1 — `Formula`

```agda
data Formula : Set where
  var  : ℕ → Formula
  ¬f_  : Formula → Formula
  _∧f_ : Formula → Formula → Formula
  _∨f_ : Formula → Formula → Formula

infix  9 ¬f_
infixr 7 _∧f_
infixr 6 _∨f_
```

Direct translation of the grammar:

```
Formula → Var n | ¬ Formula | Formula ∧ Formula | Formula ∨ Formula
```

The constructors carry the labels `f` (for "formula") so that the boolean
operators `_∧_`, `_∨_` keep their usual meaning on `Bool`. The precedence
declarations recover the standard mathematical reading: `¬ x ∨ y ∧ z`
parses as `(¬ x) ∨ (y ∧ z)`.

**Beginner tip.** Whenever the project gives you a BNF‑style grammar, the
first instinct should be to mirror the productions one‑for‑one as
constructors of an inductive type. That gives you an unambiguous,
case‑splittable representation immediately.

---

## 4. Problem 2 — `Literal`, `NNF`

```agda
data Literal : Set where
  pos : ℕ → Literal
  neg : ℕ → Literal

data NNF : Set where
  lit  : Literal → NNF
  _∧n_ : NNF → NNF → NNF
  _∨n_ : NNF → NNF → NNF
```

A *literal* is a variable or a negated variable. An NNF formula is built
from literals using only `∧` and `∨`. The point of NNF is to **forbid
negations except in front of variables**, which is exactly what `Literal`
encodes.

**Why two types instead of one?** Because typing rules out illegal terms.
With `NNF` defined this way, **it is impossible to construct an NNF term
with a negation inside an `∧` or `∨` subtree**. The invariant is enforced
by the type, not by an external proof.

---

## 5. Problem 3 — `to-nnf`

The translation uses two **mutually recursive** helpers:

```agda
nnf⁺ : Formula → NNF      -- equivalent to       φ
nnf⁻ : Formula → NNF      -- equivalent to     ¬ φ
```

Going through the cases of `Formula`:

| Case                | `nnf⁺`              | `nnf⁻`                |
|---------------------|---------------------|-----------------------|
| `var n`             | `lit (pos n)`       | `lit (neg n)`         |
| `¬f φ`              | `nnf⁻ φ`            | `nnf⁺ φ` (`¬¬φ ≡ φ`)  |
| `a ∧f b`            | `nnf⁺ a ∧n nnf⁺ b`  | `nnf⁻ a ∨n nnf⁻ b`    |
| `a ∨f b`            | `nnf⁺ a ∨n nnf⁺ b`  | `nnf⁻ a ∧n nnf⁻ b`    |

The `nnf⁻` cases are De Morgan’s laws. The top-level translation is
`to-nnf = nnf⁺`.

**Why is this accepted by the termination checker?** Both helpers recurse
only on **strictly smaller** subformulas of `Formula`. Even though they
call each other, the *argument* always shrinks.

---

## 6. Problem 4 — `Assoc` (week-9 module, completed)

The project says: *"Copy the `Assoc` module from week 9 exercises and
complete it"*. Ex9 ships **two** module skeletons:

- `module AssocList (K : DecType) (V : Set)` — most of the structure is
  there but with holes;
- `module Assoc (K : DecType) (V : Set)` — every body is `{!!}`.

The student is expected to complete `AssocList` (or write their own
`Assoc` from scratch). We do the former because every Ex9 hole has an
obvious good implementation.

### 6.1 `DecType`: a "type with decidable equality"

```agda
record DecType : Set₁ where
  field
    carr   : Set
    test-≡ : (x y : carr) → Dec (x ≡ y)
```

This is a *bundle*: the type itself and a decision procedure for equality
on that type. Without `test-≡` we can’t implement `_∈?_` (we couldn’t check
whether a key is already in the list).

`Set₁` is Agda’s next universe up; it’s there only because `DecType` has a
field of type `Set`. You can read `Set₁` as "the type of class‑like
records over `Set`" and move on.

### 6.2 The membership relation `_∈_`

```agda
infix 4 _∈_
data _∈_ : carr K → Assoc → Set where
  here  : ∀ {k v kvs}     → k ∈ ((k  , v ) ∷ kvs)
  there : ∀ {k k′ v′ kvs} → k ∈ kvs → k ∈ ((k′ , v′) ∷ kvs)
```

A **proof‑relevant membership relation**. A value of `k ∈ kvs` is literally
a *path into the list* that points at the first pair whose key is `k`.
This is the standard way to express set/list membership in dependent type
theory.

### 6.3 `lookup` from a membership proof

```agda
lookup : {k : carr K} {kvs : Assoc} → k ∈ kvs → V
lookup {kvs = (_ , v) ∷ _}   here      = v
lookup {kvs = (_ , _) ∷ kvs} (there p) = lookup {kvs = kvs} p
```

Because the membership proof itself **witnesses** that the key is in the
list, `lookup` is total: there is no `nothing` case.

### 6.4 Decidable membership `_∈?_`

```agda
_∈?_ : (k : carr K) → (kvs : Assoc) → Dec (k ∈ kvs)
k ∈? [] = no (λ ())
k ∈? ((k′ , _) ∷ kvs) with test-≡ K k k′
... | yes refl = yes here
... | no  k≢k′ with k ∈? kvs
...   | yes p  = yes (there p)
...   | no  ¬p = no λ where
          here      → k≢k′ refl
          (there q) → ¬p q
```

We walk the list. At each cons we compare the head key with `k` using
`test-≡`. If it matches, `yes here` (note `refl` unifies the two keys).
Otherwise we recurse and lift the answer with `there` / refute both ways.

### 6.5 `_‼_` and `_[_]≔_`

```agda
_‼_ : Assoc → carr K → Maybe V
kvs ‼ k with k ∈? kvs
... | yes p = just (lookup p)
... | no  _ = nothing

_[_]≔_ : Assoc → carr K → V → Assoc
[]                 [ k ]≔ v = (k , v) ∷ []
((k′ , v′) ∷ kvs) [ k ]≔ v with test-≡ K k k′
... | yes _ = (k  , v ) ∷ kvs
... | no  _ = (k′ , v′) ∷ (kvs [ k ]≔ v)
```

`_‼_` packs the decidable membership and `lookup` into the familiar
`Maybe`-returning lookup. `_[_]≔_` walks the list, replaces the value at
the first matching key, or appends at the end if no key matches.

### 6.6 Instantiating with `ℕ` and `Bool`

```agda
𝒩 : DecType
carr   𝒩 = ℕ
test-≡ 𝒩 = _≟_

open AssocList 𝒩 Bool public hiding (lookup)

Assignment : Set
Assignment = Assoc
```

We use the standard library’s decidable equality `_≟_ : (m n : ℕ) → Dec
(m ≡ n)` and re-export `Assoc` so the rest of the file can talk about
`Assignment`.

`hiding (lookup)` keeps the slot free for the top-level Maybe-style
`lookup` used by Problems 5–10:

```agda
empty  : Assignment
empty  = []

insert : ℕ → Bool → Assignment → Assignment
insert k v ρ = ρ [ k ]≔ v

lookup : ℕ → Assignment → Maybe Bool
lookup k ρ = ρ ‼ k
```

### 6.7 First‑timer commentary

- The membership proof carries *information*, not just truth. Once you
  have a proof, `lookup` cannot fail. The standard library’s `Any` and
  `All` predicates generalize this pattern.
- Dependent records (like `DecType`) are how you parametrize modules by
  "an algebraic structure": carrier set + operations + laws.
- `with test-≡ K k k′ ... | yes refl` is the crucial idiomatic move: the
  `refl` pattern *changes the goal* by unifying `k` with `k′`. Without
  pattern matching on `refl`, the `yes here` step wouldn’t typecheck.

---

## 7. Problem 5 — `eval : Assignment → Formula → Maybe Bool`

```agda
eval : Assignment → Formula → Maybe Bool
eval ρ (var n)   = lookup n ρ
eval ρ (¬f φ)    with eval ρ φ
... | just b  = just (not b)
... | nothing = nothing
eval ρ (a ∧f b)  with eval ρ a | eval ρ b
... | just x | just y = just (x and y)
... | _      | _      = nothing
eval ρ (a ∨f b)  with eval ρ a | eval ρ b
... | just x | just y = just (x or y)
... | _      | _      = nothing
```

`Maybe Bool` is **three‑valued logic**: `just true`, `just false`, or
`nothing`. The convention used here is:

- a single undefined variable poisons the whole formula with `nothing`;
- otherwise the boolean operators on `Bool` give the answer.

(Some semantics short‑circuit: `false and _ = false` even if the second
argument is undefined. The project does not require that; the simpler
"both defined" rule is acceptable and is what we use.)

---

## 8. Problem 6 — `eval-nnf : Assignment → NNF → Maybe Bool`

We split off a literal evaluator and reuse the same `and`/`or` pattern:

```agda
eval-lit : Assignment → Literal → Maybe Bool
eval-lit ρ (pos n) = lookup n ρ
eval-lit ρ (neg n) with lookup n ρ
... | just b  = just (not b)
... | nothing = nothing

eval-nnf : Assignment → NNF → Maybe Bool
eval-nnf ρ (lit ℓ)   = eval-lit ρ ℓ
eval-nnf ρ (a ∧n b)  with eval-nnf ρ a | eval-nnf ρ b
... | just x | just y = just (x and y)
... | _      | _      = nothing
eval-nnf ρ (a ∨n b)  with eval-nnf ρ a | eval-nnf ρ b
... | just x | just y = just (x or y)
... | _      | _      = nothing
```

This evaluator is a "structural copy" of `eval`. The `¬f_` case from
Problem 5 has now collapsed into the literal evaluator, because the type
**`NNF`** guarantees negations only ever appear in front of variables.

---

## 9. Problem 7 — `CNF`

The project’s grammar reads:

```
Disjunct → Literal | Literal ∨ Disjunct
CNF      → Disjunct ∨ CNF
```

This has a **typo** and a **missing base case**. CNF should be a
*conjunction* of disjuncts:

```agda
data Disjunct : Set where
  lit  : Literal → Disjunct
  _∨d_ : Literal → Disjunct → Disjunct

data CNF : Set where
  dis  : Disjunct → CNF
  _∧c_ : Disjunct → CNF → CNF

infixr 6 _∨d_
infixr 7 _∧c_
```

- We use `∧c` (not `∨c`) for the CNF connective; "CNF = conjunctive
  normal form".
- We add `dis : Disjunct → CNF` so that the grammar actually generates
  non‑empty CNFs.
- The `Disjunct` and `CNF` types are **non‑empty cons lists** of
  literals and disjuncts, respectively. This is preferable to
  `List Disjunct` because it rules out empty disjuncts/CNFs at the type
  level — and that is exactly the invariant required by classical CNF.

---

## 10. Problem 8 — `eval-cnf : Assignment → CNF → Maybe Bool`

```agda
eval-disjunct : Assignment → Disjunct → Maybe Bool
eval-disjunct ρ (lit ℓ)   = eval-lit ρ ℓ
eval-disjunct ρ (ℓ ∨d d)  with eval-lit ρ ℓ | eval-disjunct ρ d
... | just x | just y = just (x or y)
... | _      | _      = nothing

eval-cnf : Assignment → CNF → Maybe Bool
eval-cnf ρ (dis d)   = eval-disjunct ρ d
eval-cnf ρ (d ∧c φ)  with eval-disjunct ρ d | eval-cnf ρ φ
... | just x | just y = just (x and y)
... | _      | _      = nothing
```

The structure is identical to `eval-nnf`: walk the term, evaluate the
pieces, combine with `and`/`or`. Again "all variables must be defined"
is what `Maybe` enforces.

---

## 11. Problem 9 — SAT solver (splitting / DPLL)

We extract every variable from the CNF, deduplicate, and search:

```agda
sat-search : List ℕ → Assignment → CNF → Bool
sat-search [] ρ φ with eval-cnf ρ φ
... | just true  = true
... | _          = false
sat-search (v ∷ vs) ρ φ =
      sat-search vs (insert v true  ρ) φ
   or sat-search vs (insert v false ρ) φ

sat? : CNF → Bool
sat? φ = sat-search (dedup (cnf-vars φ)) empty φ
```

This is the **splitting rule** at the heart of DPLL: pick a variable,
recursively try both polarities. Termination is structural on the list
of remaining variables. Adding unit propagation / pure literal
elimination is a strict refinement and is worth a note in the report.

---

## 12. Problem 10 — Tseytin transformation

For every internal node of the NNF we introduce a fresh variable `x` and
emit three clauses encoding `x ↔ (la ∧ lb)` or `x ↔ (la ∨ lb)`:

| `x ↔ (la ∧ lb)`        | `x ↔ (la ∨ lb)`         |
|------------------------|-------------------------|
| `¬x ∨ la`              | `¬x ∨ la ∨ lb`          |
| `¬x ∨ lb`              | `¬la ∨ x`               |
| `¬la ∨ ¬lb ∨ x`        | `¬lb ∨ x`               |

The auxiliary recursion threads a "next free variable" counter through
the tree, returns the top-level literal `top` representing the whole
subformula, and accumulates clauses. The final CNF asserts `top` plus
all generated clauses.

**Equisatisfiable, not equivalent.** Tseytin adds fresh variables, so it
doesn’t produce an equivalent formula over the original variables — only
one whose models project to models of the input. That is what SAT
solving needs and is the whole point of using Tseytin instead of a naïve
distribution that explodes exponentially.

---

## 13. Audit of Problems 5–8

| Problem | Status   | Issues / suggestions |
|--------:|:---------|:---------------------|
| 5 `eval`        | ✅ Correct | Acceptable as is. Could be tightened using `Maybe`’s monadic `_>>=_` for less repetition. |
| 6 `eval-nnf`    | ✅ Correct | Same shape as Problem 5; the dedicated `eval-lit` helper is the right factoring. |
| 7 `CNF` type    | ✅ Correct | Project grammar has a typo (`CNF → Disjunct ∨ CNF`) and no base case. We use `∧` and add `dis : Disjunct → CNF`. **Should be flagged in the report.** |
| 8 `eval-cnf`    | ✅ Correct | Same pattern as `eval-nnf`; total semantics ("nothing if any variable is undefined") is consistent with the rest. |

Nothing in 5–8 is wrong, but two improvements are worth considering:

1. **`Maybe` monad refactor.** The 4-way `with eval ρ a | eval ρ b`
   blocks repeat the same pattern three times. Using
   `open import Data.Maybe.Categorical` (or just defining your own
   `_>>=_` once) reduces each block to two lines.
2. **Short-circuit semantics.** If you want `false and _ = false` even
   when the second argument is `nothing`, you must change the `with`
   blocks to inspect the first result before the second. The project
   does not require this.

---

## 14. End-to-end mental model

```
       Formula  ──── to-nnf ──────►  NNF  ──── tseytin ──►  CNF
          │                          │                       │
          │ eval                     │ eval-nnf              │ eval-cnf
          ▼                          ▼                       ▼
                          Maybe Bool                         │
                                                             │ sat?
                                                             ▼
                                                            Bool
```

- All three evaluators consume an `Assignment` and return `Maybe Bool`.
- `to-nnf` is **equivalent** (preserves truth value).
- `tseytin` is **equisatisfiable** (adds fresh variables; preserves
  satisfiability, not truth value).
- `sat?` decides satisfiability of any CNF.

---

## 15. First-time coder checklist

When you write or extend a function in `Solution.agda`:

1. **Read the type first.** The signature is the contract; the body is the
   implementation. Write the signature, save, see what Agda complains about.
2. **Pattern-match on the outermost constructor.** That is what enables
   structural recursion; it is also what Agda checks termination against.
3. **Use `with` to peek at intermediate `Maybe`/`Dec` values.** Don’t try
   to chain `case` expressions; `with` is the right tool.
4. **Leave a `?` when stuck.** With `agda-mode`, load the file and the hole
   tells you the goal type and the variables in scope.
5. **`refl` in patterns is powerful.** When `test-≡ K k k′` returns
   `yes refl`, Agda replaces every occurrence of `k′` with `k` (and vice
   versa) in the rest of that clause. That is how `yes here` typechecks
   in `_∈?_`.
6. **Implicit arguments are not optional.** If Agda complains about an
   unsolved metavariable, you probably need to pass an implicit
   explicitly: `lookup {kvs = kvs} p`.
7. **The termination checker is your friend.** If it complains, your
   recursion isn’t on a strictly smaller term. The fix is almost always
   to introduce an explicit accumulator argument that decreases.

Happy hacking.
