# Problem 11 — NNF → CNF (Tseytin)

Koda: `src/Solution.agda` (Problem 11).  
Vizualizacija: [problem11-visual.html](problem11-visual.html) (korak za korakom po drevesu NNF).

---

## Kaj je cilj?

Pretvori NNF v CNF tako, da:

- število klavzul raste **linearno** (ne eksponentno kot pri naivni distribuciji);
- original in CNF sta **equisatisfiabilna** (ista resničnostna vrednost, morda z dodatnimi spremenljivkami).

Formalnega dokaza equisatisfiabilnosti v Agdi **ne** delamo.

---

## Ideja v enem stavku

Za vsako notranje vozlišče NNF uvedemo svežo spremenljivko `xᵢ` in dodamo klavzule, ki kodirajo  
`xᵢ ↔ (podformula)`.

Listi (literali) ostanejo sami — brez nove spremenljivke.

---

## Faze v kodi

### 1. Pomožno

| Funkcija | Vloga |
|----------|--------|
| `flip-lit` | `pos n` ↔ `neg n` (za klavzule tipa ¬la ∨ …) |
| `max-var` | največji indeks v NNF — sveže spremenljivke gredo **nad** to |
| `clauses-to-cnf` | seznam klavzul → CNF z `∧c` |

### 2. `tseytin : NNF → ℕ → ℕ × Literal × List Disjunct`

Rekurzija po NNF. Številka `n` je “naslednji prosti indeks”.

**List `lit ℓ`:** vrne isti literal, brez novih klavzul.

**Vozlišče `a ∧n b`:** po rekurziji imaš literale `la`, `lb` (predstavnika podformul). Nova spremenljivka `x` na indeksu `suc n₂`. Tri klavzule:

| Klavzula | Logično |
|----------|---------|
| `¬x ∨ la` | x → la |
| `¬x ∨ lb` | x → lb |
| `¬la ∨ ¬lb ∨ x` | la ∧ lb → x |

Skupaj: **x ↔ (la ∧ lb)**.

**Vozlišče `a ∨n b`:** še tri klavzule:

| Klavzula | Logično |
|----------|---------|
| `¬x ∨ la ∨ lb` | x → la ∨ lb |
| `¬la ∨ x` | la → x |
| `¬lb ∨ x` | lb → x |

Skupaj: **x ↔ (la ∨ lb)**.

### 3. `to-cnf`

```agda
to-cnf φ = clauses-to-cnf (lit root) cs
  where tseytin φ (suc (max-var φ)) = _, root, cs
```

- Začneš z indeksom **nad** vsemi starimi spremenljivkami.
- `root` je literal korena (nova ali stara spremenljivka).
- Prva klavzula CNF je `lit root`; ostale so zbrane klavzule.

---

## Primer (intuicija)

NNF: `(x₀ ∧n x₁)` (oba lista).

1. `tseytin x₀` → literal `pos 0`, brez klavzul.
2. `tseytin x₁` → `pos 1`, brez klavzul.
3. Za `∧`: nova `x₂`, klavzule za `x₂ ↔ (x₀ ∧ x₁)`.
4. CNF ≈ `x₂ ∧ (¬x₂∨x₀) ∧ (¬x₂∨x₁) ∧ (¬x₀∨¬x₁∨x₂)`.

Če zadovoljiš original, nastaviš tudi `x₂`; obratno velja podobno (equisat, ne enakovrednost).

---

## Zakaj ne naivna distribucija?

`(a ∨ b) ∧ c` → distribucija lahko eksplodira. Tseytin doda **O(število vozlišč)** klavzul in spremenljivk.

---

## Povezava z Problem 12

Problem 12 kliče `to-cnf (to-nnf φ)` — brez Tseytina bi CNF lahko postal prevelik ali težak za SAT.
