# Problem 12 — SAT za poljubno `Formula`

Koda: `src/Solution.agda` (Problem 12).  
Vizualizacija: [problem12-visual.html](problem12-visual.html) (cevovod + dokaz).

---

## Kaj je cilj?

Solver za **poljubno** `Formula` (ne samo CNF), z rezultatom, ki nosi dokaz na **originalni** formuli.

---

## Cevovod (4 koraki)

```
φ : Formula
    ↓ to-nnf
NNF
    ↓ to-cnf      (Tseytin, Problem 11)
CNF
    ↓ sat?        (DPLL, Problem 9)
SatResult
    ↓ eval ρ φ    (ponovna preverba!)
FormulaSat φ
```

---

## Tip `FormulaSat`

Enako filozofija kot `SatResult`, a dokaz govori o `eval` na `Formula`:

```agda
data FormulaSat (φ : Formula) : Set where
  sat   : (ρ : Assignment) → eval ρ φ ≡ just true → FormulaSat φ
  unsat : FormulaSat φ
```

**Pomembno:** dokaz v `sat ρ p` je `eval ρ φ ≡ just true`, **ne** `eval-cnf`.

---

## Zakaj ponovni `eval ρ φ`?

Tseytinovo equisatisfiabilnost **ni** formalno dokazana. CNF-solver lahko vrne ρ, ki zadovolji CNF, a brez preverbe ne vemo, ali drži za original.

Zato:

```agda
sat-formula? φ with sat? (to-cnf (to-nnf φ))
... | unsat   = unsat
... | sat ρ _ with eval ρ φ in eq
...   | just true = sat ρ eq      -- eq je pravi dokaz za Formula
...   | _         = unsat
```

| Korak | Kaj pomeni |
|-------|------------|
| `unsat` iz CNF | v tem modelu rečemo unsat za Formula |
| `sat ρ _` + `eval … just true` | ρ potrjeno na originalu → `sat ρ eq` |
| `sat ρ _` + eval ≠ true | CNF rešitev ne prenese → `unsat` |

Zdravost je spet **po konstrukciji**: `sat ρ eq` zahteva `eq : eval ρ φ ≡ just true`.

Lema `sat-formula?-sound` = ista zgodba kot `sat?-sound`.

---

## `solve`

```agda
solve : Formula → Maybe Assignment
```

Vrne samo `just ρ` ali `nothing` — brez dokaza. Priročno za “uporabnik”, ne za Agda-dokaz.

---

## Konkreten primer (mentalno)

Formula: `var 0 ∧f var 1` (x₀ ∧ x₁).

1. `to-nnf` → NNF z `∧n`.
2. `to-cnf` → CNF + pomožne spremenljivke (Tseytin).
3. `sat?` → npr. `sat [(0,true),(1,true),…] _` (dokaz na CNF).
4. `eval ρ φ` → `just true` → `sat ρ eq` z dokazom na **Formuli**.

V HTML vizualizaciji lahko izbereš enostavno formulo in vidiš vsak korak.

---

## Povezava s prejšnjimi problemi

| Problem | Vloga v 12 |
|---------|------------|
| 3 `to-nnf` | Formula → NNF |
| 11 `to-cnf` | NNF → CNF |
| 9 `sat?` | CNF → `SatResult` |
| 10 | zdravost CNF dela (tip `SatResult`) |
| 12 | združi + dokaz na `Formula` |
