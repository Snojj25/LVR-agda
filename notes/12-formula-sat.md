# Note 12 — Problem 12: A SAT Solver for Any Formula

Problem 12: *"use the above to construct a SAT solver for any
formula."* Code: `src/Solution.agda`, Problem 12 section. Interactive
visualisation: [problem12-visual.html](problem12-visual.html)
(pipeline + proof flow).

## 1. The pipeline

Everything is already on the shelf:

```
φ : Formula
    ↓ to-nnf        (Problem 3)
NNF
    ↓ to-cnf        (Problem 11, Tseytin)
CNF
    ↓ sat?          (Problem 9, DPLL)
SatResult
    ↓ eval ρ φ      (re-check on the ORIGINAL formula!)
FormulaSat φ
```

## 2. The result type

Same philosophy as `SatResult`, but the proof now speaks about `eval`
on the original `Formula`:

```agda
data FormulaSat (φ : Formula) : Set where
  sat   : (ρ : Assignment) → eval ρ φ ≡ just true → FormulaSat φ
  unsat : FormulaSat φ
```

**Important:** the proof inside `sat ρ p` is `eval ρ φ ≡ just true` —
about the input formula, *not* about some CNF the user never saw.

## 3. The key trick: re-evaluation instead of a Tseytin proof

The CNF solver returns a ρ that satisfies `to-cnf (to-nnf φ)`. To turn
that into a proof about φ itself we would need the lemma

> `eval-cnf ρ (to-cnf (to-nnf φ)) ≡ just true  →  eval ρ φ ≡ just true`

which is exactly the (unproven, hard) correctness of Tseytin plus
`to-nnf`. Instead we reuse the cheap trick from Problem 9: **run the
candidate ρ through `eval` on the original formula** and capture the
result with `with … in eq`:

```agda
sat-formula? : (φ : Formula) → FormulaSat φ
sat-formula? φ with sat? (to-cnf (to-nnf φ))
... | unsat   = unsat
... | sat ρ _ with eval ρ φ in eq
...   | just true = sat ρ eq        -- eq is a proof about Formula
...   | _         = unsat
```

| Case | Meaning |
|------|---------|
| CNF solver says `unsat` | report `unsat` for φ |
| CNF model ρ, and `eval ρ φ ≡ just true` | ρ confirmed on the original → `sat ρ eq` |
| CNF model ρ, but `eval ρ φ` is not `just true` | defensive fallback → `unsat` |

The third row cannot actually occur — the Tseytin clauses are full
biconditionals, so a CNF model always restricts to a model of φ, and ρ
binds every original variable (each original literal appears in some
clause, so `cnf-vars` picks its variable up). But the *code* does not
need to know that: by re-checking, soundness holds **by construction**,
with zero proof effort about Tseytin.

The price of this honesty: if the impossible case ever did fire, we
would answer `unsat` wrongly — i.e. the re-check trades an unproven
*completeness* edge case for fully type-checked *soundness*. Same
trade-off as Problem 10, made consciously.

## 4. Soundness lemma and `solve`

```agda
sat-formula?-sound : ∀ {φ ρ p} → sat-formula? φ ≡ sat ρ p → eval ρ φ ≡ just true
sat-formula?-sound {p = p} _ = p
```

Same one-liner story as `sat?-sound` (note 10): the proof is already
inside the constructor.

For callers who just want an answer:

```agda
solve : Formula → Maybe Assignment
solve φ with sat-formula? φ
... | sat ρ _ = just ρ
... | unsat   = nothing
```

Note: the returned ρ may also bind fresh Tseytin variables — that is
harmless, since the proof `eval ρ φ ≡ just true` is about the original
formula (extra bindings are simply never looked up).

## 5. A concrete run

`solve (var 0)`:

1. `to-nnf (var 0) = lit (pos 0)`; `to-cnf` of a bare literal is
   `dis (lit (pos 0))` — no fresh variables.
2. `sat?` sees variable 0 occurring only positively → pure literal →
   model `(0 , true) ∷ []`.
3. Re-check: `eval ((0 , true) ∷ []) (var 0) = just true` → `sat`.
4. `solve` returns `just ((0 , true) ∷ [])`.

This exact run is pinned down as `test-solve-model` in
`src/Tests.agda`, along with a tautology, a contradiction, and a
compound pipeline test (Problem 12 section).

## 6. How the problems fit together

| Problem | Role in Problem 12 |
|---------|--------------------|
| 3 `to-nnf` | Formula → NNF (equivalence-preserving) |
| 11 `to-cnf` | NNF → CNF (equisatisfiable, linear) |
| 9 `sat?` | CNF → `SatResult` (proof-carrying search) |
| 10 | the soundness story `FormulaSat` reuses |
| 12 | composes them and re-anchors the proof on `Formula` |
