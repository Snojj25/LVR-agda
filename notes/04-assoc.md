# Note 04 — Variable Assignments and Evaluation

This note covers Problems 4, 5, and 6: the type of variable
assignments (`Assignment`) and the two evaluation functions (`eval`
for `Formula`, `eval-nnf` for `NNF`). Companion to `src/Solution.agda`,
continuing note 01 (`Formula`) and note 02 (NNF and the equivalence
theorem `eval ρ φ ≡ eval-nnf ρ (to-nnf φ)`).

Questions answered:

1. What is a "variable assignment", mathematically?
2. How do we represent one in Agda, with what trade-offs?
3. Why does `eval` return `Maybe Bool` instead of `Bool`?
4. How does `eval` work, case by case?
5. How does `eval-nnf` work, and how is it simpler?
6. How does the equivalence theorem link the two?
7. What would a `NoDup`-protected `Assoc` record cost?

---

## 1. What is an assignment?

In propositional logic an **interpretation** is a function `ρ : V → 𝟚`
where V is the set of propositional variables and 𝟚 = {true, false}.
Once ρ is fixed, every formula has a unique truth value: walk the
syntax tree, use ρ at the leaves.

Variables here are encoded as natural numbers: `Var n` is the n-th
variable, so in principle ρ : ℕ → Bool. But any concrete formula
mentions finitely many variables, so we want a **partial** function
`ρ : ℕ ⇀ Bool`. Two reasons:

- **Sparsity.** No need to invent defaults for unused variables.
  `var 7 ∨f var 12` should be evaluable from values for 7 and 12 alone.
- **Honesty.** If ρ says nothing about a variable in φ, the right
  answer is **"I do not know"** — not an arbitrary default. Hence
  `eval`'s `Maybe Bool` return (Section 3).

Partiality of ρ is why `lookup` returns `Maybe Bool` and the rest of
the file is sprinkled with `Maybe`-propagation.

---

## 2. Three reasonable representations

A spectrum from "minimal data, no invariants" to "precise types, lots
of proof obligations".

### (a) Bare list of pairs — what we ship

```agda
Assignment : Set
Assignment = List (ℕ × Bool)

empty : Assignment
empty = []

insert : ℕ → Bool → Assignment → Assignment
insert k v ρ = (k , v) ∷ ρ

lookup : ℕ → Assignment → Maybe Bool
lookup k []                = nothing
lookup k ((k′ , v) ∷ ρ)    with k ≟ k′
... | yes _ = just v
... | no  _ = lookup k ρ
```

Semantics is **first-match-wins**: `insert k v` prepends; `lookup k`
walks left-to-right and returns the first match. Re-inserting `k`
shadows the earlier value — lookups cannot tell the difference.

Good: `insert` is O(1) and trivially preserves any invariant (there
is none); `lookup` works because `_≟_ : DecidableEquality ℕ` is
decidable (Section 8); enough for Problems 5–10. Bad: stale entries
can accumulate, so proving things like "every key appears at most
once" requires extra work.

### (b) NoDup-protected list

Keep the same payload, but require no two entries share a key. We
capture that as a **predicate over lists of pairs**.

To state the predicate we need "every entry in the tail has a key
different from k". Stdlib's `All` from
`Data.List.Relation.Unary.All` does exactly that: for `P : A → Set`,
`All P xs` is the type of proofs that every element of `xs` satisfies
`P`.

```agda
open import Data.List.Relation.Unary.All using (All; []; _∷_)

Pair : Set
Pair = ℕ × Bool

Fresh : ℕ → List Pair → Set
Fresh k = All (λ p → ¬ proj₁ p ≡ k)

data NoDup : List Pair → Set where
  []  : NoDup []
  _∷_ : ∀ {p ps} → Fresh (proj₁ p) ps → NoDup ps → NoDup (p ∷ ps)
```

`Fresh k ps` reads: `k` is not the first component of any pair in
`ps`. The `NoDup` constructors say `[]` has no duplicates, and `p ∷ ps`
has no duplicates iff `p`'s key is fresh in `ps` and `ps` has no
duplicates.

The dual of `All` is `Any`, and stdlib gives decidability of both:

```agda
open import Data.List.Relation.Unary.All  using (all?)
open import Data.List.Relation.Unary.Any  using (any?)
```

`all?` lifts a decision procedure for `P` to one for `All P`. Since
`_≟_ : DecidableEquality ℕ` is decidable (free from `Data.Nat`),
`Fresh k` and `NoDup` are decidable too. We use that in the stretch
goal (Section 7).

#### The week-9 `Assoc` module

Week 9 introduced a parametric version

```agda
module Assoc {K V : Set} (_≟K_ : DecidableEquality K) where
  Pair = K × V
  ... -- empty, insert, lookup, delete, NoDup, ...
```

We are allowed to specialise to `K = ℕ`, `V = Bool`, with `_≟K_` from
`Data.Nat`. Parametric is more reusable; specialised is shorter and
covers Problems 5–10.

### (c) Total function ℕ → Bool

```agda
Assignment = ℕ → Bool
empty _ = false                          -- pick a default
insert k v ρ n with k ≟ n
... | yes _ = v
... | no  _ = ρ n
lookup k ρ = ρ k
```

Pros: O(1) lookup, no list. Cons: lose **partiality** (must bake in a
default) and **inspectability** (cannot enumerate assigned variables —
the SAT solver in Problem 9 needs that). Too coarse; the list gives
both.

---

## 3. Why `Maybe Bool`?

```agda
eval : Assignment → Formula → Maybe Bool
```

`Maybe` reflects partiality of ρ. If φ mentions a variable `v` that ρ
does not bind, returning "true" or "false" invents a value; `nothing`
is honest.

We need a propagation discipline. Connectives are not always strict
in their unknowns. Truth tables (`?` denotes unknown):

```
  ∧   | T ? F        ∨   | T ? F
  ----+------        ----+------
   T  | T ? F         T  | T T T
   ?  | ? ? F         ?  | T ? ?
   F  | F F F         F  | T ? F
```

Maximally precise: "`? ∧ F = F`" and "`? ∨ T = T`" — that is **Kleene**
three-valued logic. We adopt the simpler discipline: **any `nothing`
propagates outward**.

```
  ∧   | T ? F        ∨   | T ? F
  ----+------        ----+------
   T  | T ? F         T  | T ? T
   ?  | ? ? ?         ?  | ? ? ?
   F  | F ? F         F  | T ? F
```

Every binary connective becomes "if both sides are `just`, combine;
else `nothing`"; negation becomes "map `not` under `just`, else
`nothing`". The simplification costs nothing here: the SAT solver
calls `eval-cnf ρ φ` only with ρ total over φ's variables, so
`nothing` cannot occur.

---

## 4. `eval` for `Formula` (Problem 5)

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

Case-by-case:

- **`var n`**. Look up in ρ; `lookup` already lives in `Maybe Bool`.
- **`¬f φ`**. Recurse; map `not` under `just`. (Equivalent shorter:
  `Data.Maybe.map not (eval ρ φ)`; we use `with` for readability.)
- **`a ∧f b`**. Evaluate both; if both succeed, combine with `_and_`
  (imported from `Data.Bool`, renamed to avoid `_∧f_`).
- **`a ∨f b`**. Symmetric.

The `with`-clause evaluates *both* sub-evaluations eagerly; `eval` is
not short-circuit. Termination is structural on the formula.

---

## 5. `eval-nnf` for `NNF` (Problem 6)

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

There is **no `¬n_` constructor** on `NNF` — that is the whole point
of normal forms. Negation lives in `Literal`'s `neg`, so `not` only
appears inside `eval-lit (neg n)`.

`eval` has four constructor cases (`var`, `¬f_`, `_∧f_`, `_∨f_`);
`eval-nnf` has three (`lit`, `_∧n_`, `_∨n_`) plus `eval-lit`. Every
recursive call goes to a real sub-formula, never a "wrapped" one like
`¬f_`'s body, making inductive proofs over `NNF` shorter. The price
is on the conversion side: `to-nnf` uses mutual recursion `nnf⁺ /
nnf⁻` and De Morgan (note 02).

---

## 6. The equivalence theorem

Headline correctness for Problems 1–6:

> **For every assignment ρ and every formula φ,
> `eval ρ φ ≡ eval-nnf ρ (to-nnf φ)`.**

Converting to NNF preserves meaning under every interpretation. Note
02 stated this as a hint; here is the proof structure.

Recall

```agda
to-nnf : Formula → NNF
to-nnf = nnf⁺
```

so we want `eval ρ φ ≡ eval-nnf ρ (nnf⁺ φ)`. But `nnf⁺` recurses
mutually with `nnf⁻`, so induction must track both. Strengthen to a
pair:

```
(P)  ∀ ρ φ.   eval ρ φ      ≡ eval-nnf ρ (nnf⁺ φ)
(N)  ∀ ρ φ.   eval ρ (¬f φ) ≡ eval-nnf ρ (nnf⁻ φ)
```

(N) says "evaluating `¬φ` matches evaluating the negative-NNF
translation of φ". Both are proved together by induction on φ.

### Walk-through: the `_∧f_` case of (P)

For φ = `a ∧f b`, assume

```
P(a):  eval ρ a ≡ eval-nnf ρ (nnf⁺ a)
P(b):  eval ρ b ≡ eval-nnf ρ (nnf⁺ b)
```

LHS unfolds (definitionally, from `eval`'s `with`-clause) to

```
LHS = case (eval ρ a , eval ρ b) of
        (just x , just y) → just (x and y)
        _                 → nothing
```

Since `nnf⁺ (a ∧f b) = nnf⁺ a ∧n nnf⁺ b`, RHS unfolds symmetrically
with `eval-nnf ρ (nnf⁺ _)` in place of the two `eval` calls.
Substitute IHs componentwise inside the `case` — the sides are
syntactically equal. In Agda: "rewrite by `P(a)`; rewrite by `P(b)`;
refl".

### Walk-through: the `_∧f_` case of (N)

We want `eval ρ (¬f (a ∧f b)) ≡ eval-nnf ρ (nnf⁻ (a ∧f b))`. By
definition `nnf⁻ (a ∧f b) = nnf⁻ a ∨n nnf⁻ b` (De Morgan), so RHS is a
`case` on `eval-nnf ρ (nnf⁻ a)` and `eval-nnf ρ (nnf⁻ b)` combining
with `_or_`. LHS is "negate inside `Maybe` of `eval ρ (a ∧f b)`",
unfolding to a `case` on `eval ρ a / eval ρ b` combining with `_and_`.

Apply two facts:

- **IH (N) on `a` and `b`** rewrites `eval ρ (¬f a)`, `eval ρ (¬f b)`
  into `eval-nnf ρ (nnf⁻ a)`, `eval-nnf ρ (nnf⁻ b)`.
- **Boolean De Morgan**: `not (x and y) ≡ not x or not y` (stdlib:
  `Data.Bool.Properties.not-and-distrib`).

The negated-conjunction case of (N) reduces to the disjunction case
for negated arguments — matching `nnf⁻ (a ∧f b)`. Remaining cases
follow the dual identity `not (x or y) ≡ not x and not y`.

(P) ∧ (N) is the right strengthening because the asymmetry between
`eval` and `eval-nnf` in handling negation is exactly what (N) bridges.

---

## 7. Stretch goal — the `NoDup` version with proofs

For representation 2(b), maintain "no two pairs share a key":

```agda
record Assoc : Set where
  field
    entries : List Pair
    nodup   : NoDup entries
```

and re-implement `empty`, `insert`, `lookup` to preserve the field.

`empty`:

```agda
empty : Assoc
empty = record { entries = [] ; nodup = [] }
```

`insert k v` is the interesting one: prepending `(k , v)` directly
violates the freshness obligation if `k` is already bound. Fix:
**delete the old binding first**.

```agda
remove : ℕ → List Pair → List Pair
remove k []              = []
remove k ((k′ , v) ∷ ps) with k ≟ k′
... | yes _ = remove k ps         -- drop this entry
... | no  _ = (k′ , v) ∷ remove k ps
```

Then `insert k v ρ = (k , v) ∷ remove k ρ`. Carrying it through to
`Assoc` needs three lemmas.

### Lemma 1: removal makes the key fresh

```agda
remove-fresh : ∀ k ps → Fresh k (remove k ps)
```

Induction on `ps`. Empty: `remove k [] = []`, `Fresh k [] = []`. Cons
`(k′ , v) ∷ ps`: split on `k ≟ k′`. `yes`: `remove k ((k′ , v) ∷ ps)
= remove k ps`, IH applies. `no`: result is `(k′ , v) ∷ remove k ps`;
`Fresh k` of that is `(k′ ≢ k) ∷ IH`.

Pitfall: after the outer `with k ≟ k′`, the goal in the `yes` branch
*should* display as `Fresh k (remove k ps)` so IH applies, but since
`remove` itself uses `with`, Agda may not unfold the call — the
caller's match doesn't reach the callee's abstracted variable. You
see goals like `Fresh k (remove-list k ((k′ , v) ∷ ps) | k ≟ k′)` and
`refl` won't close it. Standard fixes:

- **`with ... | inspect ...`**: keep an explicit equality witness.
- **Lift the decision to an argument**: define
  `remove-aux : (d : Dec (k ≡ k′)) → ...`, split on `d` in the proof.
- **Use stdlib's `List.filter`** with lemmas in
  `Data.List.Relation.Unary.All.Properties` (shortest).

### Lemma 2: removal preserves `NoDup`

```agda
remove-preserves-nodup : ∀ k ps → NoDup ps → NoDup (remove k ps)
```

`remove` only drops, so freshness witnesses for survivors sub-witness
the original. The work is "shrink an `All`-proof along the spine";
stdlib's `All-resp-⊆` (in `Data.List.Relation.Unary.All.Properties`)
covers it.

### Putting them together

```agda
insertA : ℕ → Bool → Assoc → Assoc
insertA k v ρ =
  record
    { entries = (k , v) ∷ remove k (Assoc.entries ρ)
    ; nodup   = remove-fresh k (Assoc.entries ρ)
              ∷ remove-preserves-nodup k (Assoc.entries ρ) (Assoc.nodup ρ)
    }
```

The `_∷_` is the `NoDup` constructor: freshness (Lemma 1) + `NoDup` on
the tail (Lemma 2).

`lookup` itself needs no new lemmas, but proving
"`lookup k (insert k v ρ) ≡ just v`" also needs
`lookup k (remove k ps) ≡ nothing`, a small induction off Lemma 1.

We don't ship the `NoDup` version because Problems 5–10 don't need it,
but it matches week 9's parametric `Assoc` — worth re-doing to see
proof-carrying data structures in Agda.

---

## 8. The decidability bedrock: `_≟_`, `yes`, `no`

Every "compare two keys" step uses **decidable equality on ℕ**:

```agda
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary using (Dec; yes; no; ¬_)

DecidableEquality A = (x y : A) → Dec (x ≡ y)

data Dec (P : Set) : Set where
  yes : P   → Dec P
  no  : ¬ P → Dec P
```

`_≟_ : DecidableEquality ℕ` from `Data.Nat` powers every `with k ≟ k′`:

- `yes _` carries `k ≡ k′`, refining types around it.
- `no _` carries `k ≢ k′`, exactly what `Fresh` needs.

Decide, case-split, use the witness — every container with lookup
needs a `DecidableEquality` argument; without it you cannot even
*write* a lookup. `all?` and `any?` (Section 2) are higher-order
versions: given decidable `P`, decide `All P xs` / `Any P xs`.

---

## Cross-references

- Note 01 introduces `Formula`, the input of `eval`.
- Note 02 introduces `NNF` and `to-nnf`, and states the equivalence
  theorem whose proof is sketched in Section 6.
- The SAT solver in note 09 (Problem 9) is the first place we *use*
  `eval-cnf` (and through it `eval-lit`) in earnest, including that
  on a fully-bound assignment `eval-cnf` always returns `just _`.
