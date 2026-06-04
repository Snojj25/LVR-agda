# Problem 10 — pravilnost SAT-solverja

Koda: `src/Solution.agda` (Problem 10, takoj za Problem 9).  
Vizualizacija: [problem10-visual.html](problem10-visual.html)

---

## Kaj je cilj?

Preveriti, da SAT-solver **ne laže**:

- če vrne `sat ρ p`, potem ρ res zadovolji φ;
- (popolnost) če obstaja ρ, ki zadovolji φ, solver ga najde.

---

## Dva dela pravilnosti

| Del | Pomen | Pri nas |
|-----|--------|---------|
| **Zdravost** | `sat ρ p` ⇒ `eval-cnf ρ φ ≡ just true` | **Dokazano** (skoraj brez dela) |
| **Popolnost** | `eval-cnf ρ φ ≡ just true` ⇒ solver vrne `sat ρ _` | **Ni dokončano** |

---

## Zdravost — zakaj je “očitna”?

Problem 9 definira:

```agda
data SatResult (φ : CNF) : Set where
  sat   : (ρ : Assignment) → eval-cnf ρ φ ≡ just true → SatResult φ
  unsat : SatResult φ
```

Agda **ne dovoli** konstruktorja `sat ρ p`, če nimaš dokaza `p`. Solver na listu iskanja naredi:

```agda
sat-search [] ρ φ with eval-cnf ρ φ in eq
... | just true = sat ρ eq
```

`eq` je točno dokaz, ki ga `sat` zahteva. Zato je zdravost **vgrajena v tip**, ne v ločenem dokazu.

Lema `sat?-sound` samo “izlušči” dokaz, če primerjaš rezultat:

```agda
sat?-sound : ∀ {φ ρ p} → sat? φ ≡ sat ρ p → eval-cnf ρ φ ≡ just true
sat?-sound {p = p} _ = p
```

Telo je `p` — dokaz je že v konstruktorju `sat`.

---

## Popolnost — zakaj ne deluje

**Polna razlaga:** `src/Solution.agda`, Problem 10, komentarji pod `-- popolnost — zakaj ne deluje`.

**Cilj 1:** če obstaja ρ z `eval-cnf ρ φ ≡ just true`, solver vrne `sat` (ne `unsat`).

**Cilj 2:** če ni zadovoljivega ρ, vrne `unsat`.

| Razlog | Jedro |
|--------|--------|
| A | `unsat` nima dokaza v tipu |
| B | Velika indukcija na DPLL (pure, konflikt, cepitev, dvojnik) |
| C | `cnf-vars` mora biti popoln |
| D | Delni `Assignment` ≠ “vsi ρ” |

`sat-from-proof` — če že imaš dokaz `p`, zgradiš `SatResult`; to **ni** popolnost solverja.

---

## Povezava s Problem 9

| Problem 9 | Problem 10 |
|-----------|------------|
| `SatResult`, `sat?` | razlaga, zakaj je to zdravo |
| dokaz `eq` na listu | lema `sat?-sound` |

Za oddajo: zdravost je pokrita z dizajnom tipa + kratko lemo; popolnost pošteno označiš kot odprt problem (poskus v komentarjih).
