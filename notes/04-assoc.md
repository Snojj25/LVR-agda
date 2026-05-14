# Note 04 — Variable Assignments and Evaluation

Problems 4, 5, 6: the `Assignment` type and the two evaluators
(`eval` for `Formula`, `eval-nnf` for `NNF`). Code:
`src/Solution.agda` lines 108–213.

## 1. What is an assignment?

An interpretation is a function ρ from variables to truth values.
Variables are indexed by `ℕ`, so in principle `ρ : ℕ → Bool`. But any
concrete formula mentions finitely many variables, so we want a
**partial** function `ρ : ℕ ⇀ Bool`:

- **Sparsity.** No defaults for unused variables.
- **Honesty.** If ρ does not bind a variable in φ, the correct answer
  is *"I do not know"* — not an arbitrary default. Hence `Maybe Bool`.

## 2. Representation: a plain association list

`Assignment` is just a list of (key, value) pairs:

```agda
Assignment : Set
Assignment = List (ℕ × Bool)
```

So an actual `Assignment` value looks like

```agda
ρ : Assignment
ρ = (7 , true) ∷ (3 , false) ∷ []
```

### 2.0 API at a glance

Four operations. Read the table as "if you call this with these
inputs, you get out a value of this type":

| function   | inputs                       | output         | meaning                       |
| ---------- | ---------------------------- | -------------- | ----------------------------- |
| `empty`    | —                            | `Assignment`   | the assignment `[]`           |
| `lookup`   | `k : ℕ`, `ρ : Assignment`    | `Maybe Bool`   | `just v` if bound, `nothing`  |
| `insert`   | `k : ℕ`, `v : Bool`, `ρ : Assignment` | `Assignment` | ρ with `k` bound to `v` |
| `_∈ᴬ?_`    | `k : ℕ`, `kvs : List _`      | `Dec (k ∈ᴬ kvs)` | yes/no decision + witness   |

Everything else (`_∈ᴬ_`, `get`) is internal scaffolding that
`lookup` is built from. The rest of §2 walks through each piece,
focusing on **what each function's type signature is actually
saying**.

### 2.1 Reading function types

Before we dive in, a refresher on Agda's function-type syntax. Every
arrow `→` separates *one argument* from *the rest of the type*:

```
A → B → C → D
─       ───────
input   "the rest" — itself a function type
```

So `A → B → C → D` is "take an `A`, get back `B → C → D`" — i.e. a
function of three arguments returning `D`. The right-most piece (the
one after the final `→`) is the **return type**; everything to its
left is an input.

Two flavours of argument we'll see:

| syntax       | who supplies it                                | example                  |
| ------------ | ---------------------------------------------- | ------------------------ |
| `A → …`      | **explicit** — *you* pass a value of type `A`  | `lookup 7 ρ`             |
| `{x : A} → …`| **implicit** — *Agda* fills it in from context | `get {kvs = …} (inj₁ _)` |
| `(x : A) → …`| explicit, but Agda gives the argument a *name* it can mention in later types | `(k : ℕ) → … k …` |

The first two carry the same value; only how you write the call
differs. The named form `(k : ℕ)` matters when *later types* in the
signature mention `k` (dependent types — see `_∈ᴬ?_` below).

### 2.2 `_∈ᴬ_` — a function that returns a *type*

```agda
_∈ᴬ_ : ℕ → List (ℕ × Bool) → Set
k ∈ᴬ []               = ⊥
k ∈ᴬ ((k′ , _) ∷ kvs) = (k ≡ k′) ⊎ (k ∈ᴬ kvs)
```

> **In:** a key `k : ℕ`, a list `kvs : List (ℕ × Bool)`.
> **Out:** a **type** (`Set`).

Yes — `_∈ᴬ_` returns a *type*, not a value. This is the dependent-
type feature: in Agda, types can be computed from values.

What type does it return? It depends on `kvs`:

- If `kvs = []`, it returns `⊥` (the empty type — no values exist).
- If `kvs = (k′ , _) ∷ rest`, it returns the sum type
  `(k ≡ k′) ⊎ (k ∈ᴬ rest)`. The proposition "*`k` is in this list*"
  is then satisfied by either "the head's key matches" (left of `⊎`)
  or "`k` is in the tail" (right of `⊎`, recursively).

Concrete example. With `kvs = (7 , true) ∷ (3 , false) ∷ []`:

```
7 ∈ᴬ kvs   unfolds to   (7 ≡ 7) ⊎ ((7 ≡ 3) ⊎ ⊥)
```

A *value* of this type — i.e. a proof that 7 is in the list — is
e.g. `inj₁ refl` (the left choice, with `refl` proving `7 ≡ 7`).

| call                   | what type comes back                         |
| ---------------------- | -------------------------------------------- |
| `7 ∈ᴬ []`              | `⊥`                                          |
| `7 ∈ᴬ ((7, _) ∷ [])`   | `(7 ≡ 7) ⊎ ⊥`                                |
| `7 ∈ᴬ ((3, _) ∷ [])`   | `(7 ≡ 3) ⊎ ⊥`                                |
| `7 ∈ᴬ ((3,_)∷(7,_)∷[])`| `(7 ≡ 3) ⊎ ((7 ≡ 7) ⊎ ⊥)`                    |

A proof of `k ∈ᴬ kvs` is therefore always a chain `inj₂ (inj₂ …
(inj₁ refl))`: a run of `inj₂`s (skip non-matching entries) ending
in `inj₁ refl` at the matching position.

### 2.3 `get` — turn a membership proof into the bound value

```agda
get : {k : ℕ} {kvs : List (ℕ × Bool)} → k ∈ᴬ kvs → Bool
```

> **In:** *(implicit)* `k`, `kvs`, *(explicit)* a proof `k ∈ᴬ kvs`.
> **Out:** the `Bool` bound to `k` in `kvs`.

Three things going on in the signature:

1. `{k : ℕ}` and `{kvs : List (ℕ × Bool)}` — *implicit* arguments.
   Agda infers `k` and `kvs` from the *type of the proof* you pass.
   When you call `get someProof`, you write nothing extra; Agda
   reads off `k` and `kvs` from `someProof`'s type.
2. `k ∈ᴬ kvs → Bool` — the explicit input is a proof, and the
   output is the bound value.
3. The proof's type *depends on* the implicit args (`k`, `kvs`).
   This is why they're listed: the type `k ∈ᴬ kvs` mentions them.

Concrete example:

```agda
ρ = (7 , true) ∷ (3 , false) ∷ []

proof : 7 ∈ᴬ ρ
proof = inj₁ refl       -- head matches

value : Bool
value = get proof       -- = true
```

When you wrote `get proof`, Agda looked at `proof`'s type
(`7 ∈ᴬ ρ`), so `k = 7` and `kvs = ρ` were filled in automatically.

The function body:

```agda
get {kvs = []}              ()
get {kvs = (_ , v) ∷ _}     (inj₁ _) = v
get {kvs = (_ , _) ∷ kvs}   (inj₂ p) = get p
```

The `{kvs = …}` syntax is Agda's way of letting you **pattern-match
on an implicit argument** — usually you'd ignore implicits, but here
the proof's shape depends on whether `kvs` is empty or a cons, so
we have to look at both.

- `kvs = []` — proof has type `⊥`, no constructor fits, absurd `()`.
- `kvs = (_ , v) ∷ _`, proof is `inj₁ _` — return the head's value
  `v`.
- `kvs = (_ , _) ∷ kvs`, proof is `inj₂ p` — recurse on the smaller
  proof `p : k ∈ᴬ kvs`.

### 2.4 `Dec` — a yes/no answer that carries its evidence

```agda
data Dec (P : Set) : Set where
  yes : P   → Dec P
  no  : ¬ P → Dec P
```

> A `Dec P` is **one of two things**: either `yes p` carrying a
> proof `p : P`, or `no q` carrying a refutation `q : P → ⊥`.

Think of `Dec P` as "decidable `P`": a stronger version of `Bool`
that *justifies its answer*. `true`/`false` give you the bit; `Dec`
gives you the bit plus the witness.

### 2.5 `_∈ᴬ?_` — decide membership, step by step

This is the longest function in the Assoc section and combines
almost everything we've seen so far: dependent types, `Dec`,
pattern-matching on equality proofs, absurd patterns, refutation
lambdas, and `with`-clauses. Let's go really slowly.

#### The signature

```agda
_∈ᴬ?_ : (k : ℕ) → (kvs : List (ℕ × Bool)) → Dec (k ∈ᴬ kvs)
```

> **In:** a key `k`, a list `kvs`.
> **Out:** a value of type `Dec (k ∈ᴬ kvs)` — either `yes p` with a
> proof `p : k ∈ᴬ kvs`, or `no q` with a refutation
> `q : ¬ (k ∈ᴬ kvs)`.

Note the parenthesised `(k : ℕ)` and `(kvs : List …)`: same as the
bare `ℕ → List … →` we saw on `_∈ᴬ_`, but now we **name** the
arguments because the return type **mentions them** (`Dec (k ∈ᴬ
kvs)` — the question we're deciding depends on the inputs). The
parentheses-with-name form is required whenever a later type
references that argument.

So calling `5 ∈ᴬ? ρ` doesn't just give us a Boolean; it gives us
*evidence* either way.

#### A primer on `with`

Almost every line below uses Agda's `with`-syntax. It's just a way
to **case-split on an intermediate computation**:

```
-- Mentally read
f x with g x
... | pattern-1 = e₁
... | pattern-2 = e₂

-- as
f x = case g x of
        pattern-1 → e₁
        pattern-2 → e₂
```

The `...` on continuation lines means *"same arguments as the parent
line, just narrowed to this case branch"*. So when you see

```agda
k ∈ᴬ? ((k′ , _) ∷ kvs)  with k ≟ k′
... | yes refl = …
... | no  k≢k′ = …
```

mentally rewrite as

```
k ∈ᴬ? ((k′ , _) ∷ kvs) =
  case k ≟ k′ of
    yes refl → …
    no  k≢k′ → …
```

Multiple `with`s chain — each one narrows one more piece of state.

#### Case 1: empty list

```agda
k ∈ᴬ? [] = no λ ()
```

The output must have type `Dec (k ∈ᴬ [])`. Since `k ∈ᴬ []` unfolds
to `⊥` (the empty type), no proof can exist — so the answer is
`no`. What does `no` need? A function of type

```
¬ (k ∈ᴬ [])
  =  (k ∈ᴬ []) → ⊥           -- definition of ¬
  =  ⊥ → ⊥                    -- because k ∈ᴬ [] unfolds to ⊥
```

A function `⊥ → ⊥` has no cases to handle (because `⊥` has no
constructors), so we write it as `λ ()`. The empty parentheses are
the **absurd pattern**: *"I would have to match on `⊥`, but that's
impossible, so there's no code to write"*.

#### Case 2: cons — do the keys at the head match?

```agda
k ∈ᴬ? ((k′ , _) ∷ kvs)  with k ≟ k′
```

We pattern-match on `(k′ , _) ∷ kvs`, extracting the head's key
`k′` (the value is ignored — `_`). Then `with k ≟ k′` asks: are `k`
and `k′` equal? `_≟_` returns a `Dec (k ≡ k′)`, so we get two
sub-cases.

##### Sub-case 2a: heads match (`yes refl`)

```agda
... | yes refl = yes (inj₁ refl)
```

Two `refl`s here, doing *different* jobs:

**Left side: `yes refl` is a pattern.** `_≟_` returned
`yes <proof>`, where the proof has type `k ≡ k′`. By
pattern-matching on `refl`, Agda **unifies `k` and `k′`** in the
surrounding context — from this point on Agda treats them as the
same number. (The only way for `refl : k ≡ k′` to type-check is if
`k` and `k′` are definitionally equal, so matching `refl` makes
that equality usable.)

**Right side: `yes (inj₁ refl)` is a value.** We must produce a
value of `Dec (k ∈ᴬ ((k′ , _) ∷ kvs))`. Unfold the type:

```
k ∈ᴬ ((k′ , _) ∷ kvs)  =  (k ≡ k′) ⊎ (k ∈ᴬ kvs)
```

We want `yes <proof of this>`. Since we *know* `k = k′` (from
matching `refl` on the left), the left side of the `⊎` is
satisfiable by `refl : k ≡ k`. We wrap with `inj₁` to enter the
left side of the sum, and return `yes (inj₁ refl)`.

The **two roles of `refl`**:

- **Pattern position** (left of `=`): pattern-match an equality
  proof; performs unification.
- **Term position** (right of `=`): construct an equality proof
  (`refl : x ≡ x` for whichever `x` Agda is currently looking at).

Same keyword, opposite directions.

##### Sub-case 2b: heads differ (`no k≢k′`)

```agda
... | no  k≢k′ with k ∈ᴬ? kvs
```

The keys don't match. `_≟_` returned `no <refutation>`, which we
name `k≢k′`. Its type is

```
k≢k′ : k ≡ k′ → ⊥
```

— *"if you ever hand me a proof that `k = k′`, I can derive a
contradiction"*.

We then **recurse** on the tail with a fresh `with k ∈ᴬ? kvs`.
Two more sub-cases.

###### Sub-sub-case 2b-i: tail has `k` (`yes p`)

```agda
...   | yes p = yes (inj₂ p)
```

The recursive call returned `yes p` where `p : k ∈ᴬ kvs`. We need
a proof of `(k ≡ k′) ⊎ (k ∈ᴬ kvs)`. We have the right side, so
wrap with `inj₂`: `inj₂ p : (k ≡ k′) ⊎ (k ∈ᴬ kvs)`. Wrap that in
`yes`.

###### Sub-sub-case 2b-ii: tail doesn't have `k` (`no k∉kvs`)

```agda
...   | no  k∉kvs = no λ { (inj₁ p) → k≢k′ p
                         ; (inj₂ p) → k∉kvs p }
```

Both possibilities failed: heads differ *and* the tail doesn't
contain `k`. So `k` is not in the list at all — the answer is `no`,
but we still owe Agda a refutation. What we need is a function

```
¬ (k ∈ᴬ ((k′ , _) ∷ kvs))
  =  ((k ≡ k′) ⊎ (k ∈ᴬ kvs)) → ⊥
```

We build it with a **pattern-matching lambda**:

```
λ { (inj₁ p) → k≢k′ p
  ; (inj₂ p) → k∉kvs p }
```

This is an anonymous function that case-splits on its argument:

- If the argument is `inj₁ p` (someone claims `k = k′`), feed
  `p : k ≡ k′` to `k≢k′`, which returns `⊥`. Contradiction.
- If the argument is `inj₂ p` (someone claims `k ∈ᴬ kvs`), feed
  `p : k ∈ᴬ kvs` to `k∉kvs`, which returns `⊥`. Contradiction.

Either way we end up at `⊥`, completing the refutation. Wrap it in
`no`.

#### Worked traces

Take

```agda
ρ = (7 , true) ∷ (5 , false) ∷ []
```

**Trace A: `7 ∈ᴬ? ρ`** — succeeds at the head.

```
7 ∈ᴬ? ((7, true) ∷ (5, false) ∷ [])
  with  7 ≟ 7                    -- yes refl   (heads match)
=  yes (inj₁ refl)
```

Result has type `Dec (7 ∈ᴬ ρ)`. Calling `get` on the extracted
proof would return `true` (the head's value).

**Trace B: `5 ∈ᴬ? ρ`** — succeeds in the tail.

```
5 ∈ᴬ? ((7, _) ∷ (5, _) ∷ [])
  with  5 ≟ 7                    -- no k≢k′   (heads differ)
  with  5 ∈ᴬ? ((5, _) ∷ [])      -- recurse on tail
    with  5 ≟ 5                  -- yes refl
    →  yes (inj₁ refl)           -- inner result
  matched outer `yes p`  where p = inj₁ refl
=  yes (inj₂ (inj₁ refl))
```

Two layers of wrapping: one `inj₂` to "skip past the `(7,_)`", then
`inj₁ refl` to match the `(5,_)`.

**Trace C: `9 ∈ᴬ? ρ`** — fails at every level.

```
9 ∈ᴬ? ((7, _) ∷ (5, _) ∷ [])
  with  9 ≟ 7                    -- no k≢k′₁
  with  9 ∈ᴬ? ((5, _) ∷ [])      -- recurse
    with  9 ≟ 5                  -- no k≢k′₂
    with  9 ∈ᴬ? []
    →  no λ ()                   -- (empty case)
    matched `no k∉kvs₁`
  →  no λ { (inj₁ p) → k≢k′₂ p ; (inj₂ p) → k∉kvs₁ p }
matched outer `no k∉kvs₂`
=  no λ { (inj₁ p) → k≢k′₁ p ; (inj₂ p) → k∉kvs₂ p }
```

The final result is a refutation built by composing the inner
refutations. It works for any would-be membership proof of `9` in
ρ: such a proof would have to be `inj₁ <proof of 9 ≡ 7>` (refuted
by `k≢k′₁`) or `inj₂ <proof of 9 ∈ᴬ tail>` (refuted by the inner
refutation, recursively).

#### Summary

| call            | result                       | meaning                                 |
| --------------- | ---------------------------- | --------------------------------------- |
| `7 ∈ᴬ? ρ`       | `yes (inj₁ refl)`            | matched at the head                     |
| `5 ∈ᴬ? ρ`       | `yes (inj₂ (inj₁ refl))`     | one skip, then matched                  |
| `9 ∈ᴬ? ρ`       | `no <refutation>`            | refuted at every level                  |

`lookup` consumes this directly: on `yes p` it returns
`just (get p)`; on `no _` it returns `nothing`. The proof's
*shape* (how many `inj₂`s before the `inj₁`) tells `get` where to
walk in the list — no extra search needed.

### 2.6 `lookup` — the public Maybe interface

```agda
lookup : ℕ → Assignment → Maybe Bool
```

> **In:** key `k`, assignment ρ.
> **Out:** `just v` if `k` is bound to `v`; `nothing` otherwise.

```agda
lookup k ρ with k ∈ᴬ? ρ
... | yes p = just (get p)
... | no  _ = nothing
```

- Decide with `_∈ᴬ?_`.
- If `yes p`, extract the value with `get p`, wrap in `just`.
- If `no _`, return `nothing`.

The proof `p` from `yes p` flows straight into `get`, which is the
whole reason `_∈ᴬ_` was a proposition rather than a `Bool`: the
*witness* tells `get` where to look without re-walking the list.

Example:

```agda
ρ = (7 , true) ∷ (3 , false) ∷ []

lookup 7 ρ  =  just true
lookup 3 ρ  =  just false
lookup 5 ρ  =  nothing
```

### 2.7 `insert` — walk and replace

```agda
insert : ℕ → Bool → Assignment → Assignment
```

> **In:** key `k`, value `v`, assignment ρ.
> **Out:** ρ with `k` bound to `v` (replacing any existing binding).

```agda
insert k v []                = (k , v) ∷ []
insert k v ((k′ , v′) ∷ ρ)   with k ≟ k′
... | yes _ = (k , v) ∷ ρ
... | no  _ = (k′ , v′) ∷ insert k v ρ
```

- Empty list → just put `(k , v)` there.
- Cons whose head's key matches → **replace** the head's value.
- Cons whose head's key doesn't match → keep the head, recurse into
  the tail.

Example:

```agda
ρ₀ = []
ρ₁ = insert 7 true ρ₀      = (7 , true) ∷ []
ρ₂ = insert 3 false ρ₁     = (7 , true) ∷ (3 , false) ∷ []
ρ₃ = insert 7 false ρ₂     = (7 , false) ∷ (3 , false) ∷ []  -- replaced!
```

Last line is the point: inserting `7` again **overwrites** rather
than shadowing. That's what keeps `lookup` deterministic without a
NoDup invariant.

### 2.8 Why this matters

Three concrete payoffs from making `_∈ᴬ_` propositional (returns a
type) rather than Boolean (returns true/false):

- **Value extraction.** `get` turns a membership proof into the
  bound `Bool` in one walk. A `Bool` test would force us to walk the
  list a second time.
- **Honesty.** `lookup`'s `nothing` and `just` cases are justified
  by Agda — `just (get p)` only type-checks because `p` proves the
  key is there.
- **Reusable shape.** `_∈ᴬ_`, `inj₁`/`inj₂` is the same skeleton as
  membership in `Vec`, `List`, trees, contexts in stdlib.

## 3. Why `Maybe Bool`?

`Maybe` reflects partiality of ρ: returning `true` or `false` for an
unbound variable would invent information. We adopt the simple
discipline **any `nothing` propagates outward**:

```
∧   | T ? F        ∨   | T ? F
----+------        ----+------
 T  | T ? F         T  | T ? T
 ?  | ? ? ?         ?  | ? ? ?
 F  | F ? F         F  | T ? F
```

A more precise *Kleene* logic would say `? ∧ F = F` and `? ∨ T = T`,
but our simpler convention costs nothing here: the SAT solver only
calls `eval-cnf` on total assignments, so `nothing` cannot occur.

## 4. `eval` for `Formula` (Problem 5)

`eval` *interprets* a `Formula` value: given an assignment ρ and a
formula tree φ, it walks the tree, looks up each variable at the
leaves, and combines the results upward into a single truth value.
This is the standard **recursive interpreter** pattern: defer to ρ
at the leaves, lift host-language operations (`not`, `and`, `or`)
at the internal nodes.

### The signature

```agda
eval : Assignment → Formula → Maybe Bool
```

> **In:** an assignment ρ, a formula φ.
> **Out:** `just b` if every variable in φ is bound by ρ and φ
> evaluates to `b`; `nothing` if any variable is unbound.

### The four cases — one per constructor

```agda
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

Read each clause as *"if the formula looks like this, the value is
computed this way"*.

#### `var n` — a leaf

```agda
eval ρ (var n) = lookup n ρ
```

Defer to `ρ`. This is *the* place where partiality enters: if `ρ`
doesn't bind `n`, `lookup` returns `nothing` and that bubbles all
the way out. Everything else in `eval` is just propagating
`Maybe`-results upward.

#### `¬f φ` — negation

```agda
eval ρ (¬f φ)
  with eval ρ φ
... | just b  = just (not b)     -- known value → flip it
... | nothing = nothing          -- unknown → still unknown
```

Evaluate the child. If it's `just b`, pull `b` out, flip it with
`not` (from `Data.Bool`), and re-wrap with `just`. If it's
`nothing`, stay `nothing`.

This is the `Maybe`-`map` pattern written out by hand:
`Data.Maybe.map not (eval ρ φ)` is the one-liner, but the explicit
`with` version is what the file uses.

#### `a ∧f b` — conjunction

```agda
eval ρ (a ∧f b)
  with eval ρ a | eval ρ b
... | just x | just y = just (x and y)     -- both known
... | _      | _      = nothing            -- either unknown → unknown
```

Note the **double `with` syntax**: `with eval ρ a | eval ρ b` lets
us evaluate *two* things at once and pattern-match on both results
in the same line. The pipe `|` separates the two scrutinees.

The first clause says "both children returned `just`": extract the
booleans, AND them (`and` is `_∧_` from `Data.Bool`, renamed at the
import site to dodge the constructor `_∧f_`), re-wrap.

The second clause is a catch-all using `_` (match anything). It
covers all three "at least one is `nothing`" combinations
(`nothing | _`, `_ | nothing`, `nothing | nothing`) in a single
line.

#### `a ∨f b` — disjunction

```agda
eval ρ (a ∨f b)
  with eval ρ a | eval ρ b
... | just x | just y = just (x or y)
... | _      | _      = nothing
```

Same shape as `∧f`, replacing `and` with `or`.

### Strictness — both sides evaluated eagerly

A subtle point: this `eval` is **strict** in both children of `∧f`
and `∨f`. Even when one child is enough to determine the answer
(`false ∧ anything = false`, `true ∨ anything = true`), we still
evaluate the other and demand it be `just _` before returning
anything other than `nothing`.

Concretely, under `ρ = [(0 , false)]`,

```
eval ρ (var 0 ∧f var 1)
```

returns `nothing`, even though logically `false ∧ ? = false` is
already decided. That's the price of the simple Maybe-propagation
discipline of §3. A Kleene-style "three-valued" evaluator would
short-circuit, but it would need extra cases per connective; we
trade those off for uniform "any `nothing` propagates outward".

### Termination

`¬f φ` recurses on `φ`; `a ∧f b` and `a ∨f b` recurse on `a` and
`b`. Every recursive call goes to a strict sub-tree, so Agda's
structural termination checker accepts `eval` without any help.
(See note 01 §7.)

### A worked trace

Let

```agda
ρ = (0 , true) ∷ (1 , false) ∷ []

φ = ¬f (var 0 ∧f var 1)              -- "¬(x₀ ∧ x₁)"
```

Evaluation step by step:

```
eval ρ (¬f (var 0 ∧f var 1))
  with eval ρ (var 0 ∧f var 1)
    with eval ρ (var 0)                  -- = lookup 0 ρ = just true
       | eval ρ (var 1)                  -- = lookup 1 ρ = just false
    →  just (true and false)             -- = just false
  →  just (not false)                    -- = just true
```

So `eval ρ φ = just true`, matching the hand calculation
`¬(T ∧ F) = ¬F = T`.

Now drop variable 1 from ρ:

```agda
ρ′ = (0 , true) ∷ []
```

```
eval ρ′ (¬f (var 0 ∧f var 1))
  with eval ρ′ (var 0 ∧f var 1)
    with eval ρ′ (var 0)                 -- = just true
       | eval ρ′ (var 1)                 -- = nothing
    →  nothing                           -- catch-all clause fires
  →  nothing                             -- ¬f case also catch-all
```

`nothing` propagates outward through both levels.

## 5. `eval-nnf` for `NNF` (Problem 6)

`eval-nnf` does for `NNF` what `eval` does for `Formula`: walk the
tree, look up variables, combine. The shapes are almost identical —
same `Maybe`-propagation, same recursion pattern — but `NNF` has
**three** node kinds instead of `Formula`'s four:

| `Formula` constructor | `NNF` counterpart                |
| --------------------- | -------------------------------- |
| `var n`               | `lit (pos n)` / `lit (neg n)`    |
| `¬f_`                 | *(absent — pushed to the leaves)* |
| `_∧f_`                | `_∧n_`                           |
| `_∨f_`                | `_∨n_`                           |

So `eval-nnf` has cases for `lit`, `∧n`, and `∨n` only. The
"negate the result" logic moves into a tiny helper, `eval-lit`,
that knows how to read either polarity of literal.

### `eval-lit` — evaluate a single literal

```agda
eval-lit : Assignment → Literal → Maybe Bool
```

> **In:** ρ, a literal `ℓ`. **Out:** `just (truth value of ℓ)` or
> `nothing`.

```agda
eval-lit ρ (pos n) = lookup n ρ
eval-lit ρ (neg n) with lookup n ρ
... | just b  = just (not b)
... | nothing = nothing
```

Two cases, one per `Literal` constructor:

- **`pos n`** — the literal is just `Var n`. Look it up; whatever ρ
  says, that's the answer.
- **`neg n`** — the literal is `¬ Var n`. Look up, then flip the
  result with `not` (propagating `nothing` if the variable is
  unbound).

This is the **only** place `not` appears in the entire NNF stack.
Once negations have been pushed to the leaves (note 02), evaluation
no longer needs an outer "negate the result" wrapper at any
internal node — that work is done once, at the leaf, in
`eval-lit (neg n)`.

### `eval-nnf` — evaluate the NNF tree

```agda
eval-nnf : Assignment → NNF → Maybe Bool
```

> **In:** ρ, an NNF formula ψ. **Out:** `just (truth value)` or
> `nothing`.

```agda
eval-nnf ρ (lit ℓ)   = eval-lit ρ ℓ
eval-nnf ρ (a ∧n b)  with eval-nnf ρ a | eval-nnf ρ b
... | just x | just y = just (x and y)
... | _      | _      = nothing
eval-nnf ρ (a ∨n b)  with eval-nnf ρ a | eval-nnf ρ b
... | just x | just y = just (x or y)
... | _      | _      = nothing
```

- **`lit ℓ`** — defer to `eval-lit`. `eval-nnf` itself never sees
  the difference between `pos` and `neg`; polarity is `eval-lit`'s
  problem.
- **`a ∧n b`** — evaluate both, AND them, propagate `nothing`.
  Identical in shape to `eval`'s `∧f` case modulo the constructor
  name.
- **`a ∨n b`** — same, with `or`.

There is no `¬n_` constructor on `NNF` (the whole point of normal
form), so there's no `eval-nnf ρ (¬n ψ)` case to write. Compared
with `eval` on `Formula`, exactly one constructor case has been
eliminated — and it's the one with the wrapping/unwrapping that
made `eval`'s `¬f φ` case stand out.

### Why this is simpler than `eval`

Two practical consequences of dropping the `¬f_` case:

1. **Fewer constructor cases for proofs.** Any induction over
   `NNF` has three cases (`lit`, `∧n`, `∨n`) instead of `Formula`'s
   four. The equivalence theorem of §6 is shorter because of this.
2. **`not` appears exactly once.** Algorithms that care about
   polarity (DPLL pure-literal elimination, the Tseytin transform
   of note 06) have direct access to it at the leaves — they read
   `pos n` / `neg n` instead of detecting `¬f` at some internal
   node.

### A worked trace

Let

```agda
ρ = (0 , true) ∷ (1 , false) ∷ []

ψ : NNF
ψ = (lit (neg 0)) ∨n (lit (pos 1))     -- "¬x₀ ∨ x₁"
```

Evaluation:

```
eval-nnf ρ ((lit (neg 0)) ∨n (lit (pos 1)))
  with eval-nnf ρ (lit (neg 0))         -- = eval-lit ρ (neg 0)
                                        -- = lookup 0 ρ = just true
                                        --   then not  = just false
     | eval-nnf ρ (lit (pos 1))         -- = eval-lit ρ (pos 1)
                                        -- = lookup 1 ρ = just false
  →  just (false or false)              -- = just false
```

Result: `just false`. Hand check: `¬x₀ ∨ x₁ = ¬T ∨ F = F ∨ F = F`. ✓

### Sanity check: `eval` and `eval-nnf` agree

The equivalence theorem of §6 says: for any ρ and any φ,

```
eval ρ φ  ≡  eval-nnf ρ (to-nnf φ)
```

— converting to NNF *before* evaluating gives the same answer.
Pushing negations to the leaves doesn't change meaning, only
shape; both interpreters read off the same truth value, just via
slightly differently-shaped trees.

## 6. The equivalence theorem

> **For every assignment ρ and every formula φ,
> `eval ρ φ ≡ eval-nnf ρ (to-nnf φ)`.**

Since `to-nnf = nnf⁺` recurses mutually with `nnf⁻`, induction must
track both. Strengthen to the pair:

```
(P)  eval ρ φ      ≡ eval-nnf ρ (nnf⁺ φ)
(N)  eval ρ (¬f φ) ≡ eval-nnf ρ (nnf⁻ φ)
```

(N) bridges the asymmetry: `eval` handles negation by an outer `not`,
while `eval-nnf` has no outer negation, so we need a separate claim
for the "applied to ¬φ" case. Both are proved together by induction
on φ.

**`_∧f_` case of (P)** is direct: both sides unfold to "lift `_and_`
over `Maybe`", and the IHs make the arguments match.

**`_∧f_` case of (N)** is the interesting one: LHS unfolds to
`not (x and y)` (under `Maybe`), RHS to `(not x) or (not y)` via
`nnf⁻ (a ∧f b) = nnf⁻ a ∨n nnf⁻ b`. They match by Boolean De Morgan.

## 7. The decidability bedrock

Every key comparison uses `_≟_ : DecidableEquality ℕ` from
`Data.Nat`. Its type:

```
_≟_ : (m n : ℕ) → Dec (m ≡ n)
```

> **In:** two naturals. **Out:** `yes` with a proof they're equal,
> or `no` with a proof they're not.

`with k ≟ k′` splits into `yes refl` (carrying `k ≡ k′`, with `refl`
unifying the two so they become identifiable in the goal) and `no
k≢k′` (carrying `k ≢ k′ = k ≡ k′ → ⊥`). Without decidable equality
on keys you cannot even *write* a `lookup`.
