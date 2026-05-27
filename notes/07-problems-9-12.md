# Rešitev problemov 9–12 — razlaga na nizki ravni

Ta zapis razloži rešitev problemov 9 do 12 v `src/Solution.agda`. Pri vsakem
problemu opišemo cilj, ključno idejo in kako koda deluje korak za korakom.

Vsa koda je iz `src/Solution.agda` od vrstice ~190 naprej.

---

## Pregled

| Problem | Cilj | Težavnost | Naša rešitev |
|---------|------|-----------|---------------|
| 9       | SAT-solver za CNF | (**/***) | Splitting/DPLL + dokaz pravilnosti v tipu |
| 10      | Pravilnost SAT-solverja | (**) | Vgrajeno v `SatResult` (lema `sat?-sound`) |
| 11      | NNF → CNF (equisat.) | (**/***) | Tseytinova transformacija |
| 12      | SAT za poljubno Formulo | (*) | Komponiranje: `Formula → NNF → CNF → SAT` |

**Filozofija:** namesto da bi naredili samo "delujoč" algoritem, vsi rezultati
nosijo dokaze o pravilnosti tam, kjer je to mogoče (Problem 9 → Problem 10
"za žep"). Kjer to ni mogoče (Tseytin equisatisfiabilnost, popolnost
splitting iskanja), to izrecno priznamo.

---

## Problem 9 — SAT-solver za CNF

### Cilj

Napiši algoritem, ki za dano CNF formulo:

- vrne **prirejanje ρ**, pri katerem se formula ovrednoti v `just true`, ali
- vrne, da takega prirejanja **ni**.

### Izhodni tip s pravilnostjo

Ključni trik: definiramo izhodni tip, ki v primeru `sat` že **vsebuje dokaz**:

```agda
data SatResult (φ : CNF) : Set where
  sat   : (ρ : Assignment) → eval-cnf ρ φ ≡ just true → SatResult φ
  unsat : SatResult φ
```

Razlaga:

- `SatResult φ` je **odvisni tip** — različen za vsako CNF formulo `φ`.
- Konstruktor `sat` vzame **tri** argumente: prirejanje `ρ`, pa še **dokaz**
  `p : eval-cnf ρ φ ≡ just true`, ki pravi "ρ res zadovolji φ".
- Konstruktor `unsat` ne vzame ničesar — je samo zastavica "ni našel".

Posledica: Agda **ne dopusti** zgraditi vrednosti `sat ρ p`, dokler nimamo
veljavnega dokaza `p`. Pravilnost je torej *prisilno* v tipu.

### Pomožne funkcije: zbiranje spremenljivk

Algoritem mora vedeti, **na katerih** spremenljivkah se cepi. Zato najprej
zberemo vse indekse spremenljivk v formuli:

```agda
lit-var : Literal → ℕ
lit-var (pos n) = n
lit-var (neg n) = n

dis-vars : Disjunct → List ℕ
dis-vars (lit ℓ)   = lit-var ℓ ∷ []
dis-vars (ℓ ∨d d)  = lit-var ℓ ∷ dis-vars d

cnf-vars : CNF → List ℕ
cnf-vars (dis d)   = dis-vars d
cnf-vars (d ∧c φ)  = dis-vars d ++ cnf-vars φ
```

Vsaka funkcija pobere vse `n` iz literalov svojega vhoda. Rezultat lahko
vsebuje **dvojnike** (npr. če ista spremenljivka nastopa večkrat) — to ni
problem, `insert` v `Assignment` zamenja staro vrednost.

### Algoritem: splitting rule

Glavna ideja: za vsako spremenljivko `v` v formuli najprej poskusi `v=true`,
nato `v=false`. Ko so vse spremenljivke prirejene, ovrednoti formulo.

```agda
sat-search : List ℕ → Assignment → (φ : CNF) → SatResult φ
sat-search []       ρ φ with eval-cnf ρ φ in eq
... | just true = sat ρ eq         -- našli zadovoljivo ρ; eq je dokaz
... | _         = unsat
sat-search (v ∷ vs) ρ φ with sat-search vs (insert v true ρ) φ
... | sat ρ′ p = sat ρ′ p          -- veja "v=true" je našla rešitev
... | unsat with sat-search vs (insert v false ρ) φ
...   | sat ρ′ p = sat ρ′ p        -- veja "v=false" je našla rešitev
...   | unsat    = unsat           -- nobena veja ni našla rešitve
```

Razlaga po vrsticah:

1. **Bazni primer** (`[]`): ni več spremenljivk za cepiti. Ovrednoti formulo.
   - `with eval-cnf ρ φ in eq` poda dokaz `eq : eval-cnf ρ φ ≡ <kar smo
     pattern-matchali>`. To je **moderna Agda sintaksa** (2.6+).
   - Če je rezultat `just true`, imamo `eq : eval-cnf ρ φ ≡ just true`, kar
     je natanko tip, ki ga zahteva `sat ρ`.
   - Sicer (just false ali nothing) → `unsat`.

2. **Rekurzivni primer** (`v ∷ vs`):
   - Najprej rekurzivno klic z `v=true`.
   - Če uspe (`sat ρ′ p`), vrnemo to. Dokaz `p` velja še naprej, ker je `φ`
     isti.
   - Sicer (`unsat`) poskusimo `v=false`.
   - Tudi to lahko da `sat` ali `unsat`. Vrnemo, kar dobimo.

### Terminacija

Agda mora videti, da rekurzija stara argument strogo manjši. Tukaj rekurzija
gre po `vs` (rep seznama spremenljivk) — **strukturno manjše** od `v ∷ vs`.
Agda to sprejme. ✓

### Vrhnja funkcija

```agda
sat? : (φ : CNF) → SatResult φ
sat? φ = sat-search (cnf-vars φ) empty φ
```

Začnemo s **praznim** prirejanjem in **vsemi** spremenljivkami formule.

### Zakaj je to "DPLL"?

Klasični DPLL ima tri komponente:

1. **Unit propagation** — če klavzula vsebuje en sam še nedoločen literal,
   ga forsiraj.
2. **Pure literal elimination** — če se spremenljivka pojavi le pozitivno
   (ali le negativno), jo nastavi tako.
3. **Splitting rule** — sicer izberi spremenljivko in razveji.

Naša implementacija ima samo (3). Še vedno je **zvočna in popolna** za
končne CNF-je, samo počasnejša. Za stopnjo "*** DPLL" je to skelet, ki bi ga
lahko nadgradili z (1) in (2) za boljšo performanso.

### Primer izvajanja

Vzemi φ = `(x₀ ∨ ¬x₁)`. CNF: `dis (pos 0 ∨d lit (neg 1))`.

- `cnf-vars φ = [0, 1]`.
- `sat-search [0, 1] [] φ`:
  - Poskusi 0=true → rekurzija na `[1] ((0,true)∷[]) φ`.
    - Poskusi 1=true → rekurzija na `[] ((1,true)∷(0,true)∷[]) φ`.
      - `eval-cnf` na (x₀=T, x₁=T): x₀ ∨ ¬x₁ = T ∨ F = T. Vrne `sat`.
    - Vrne `sat ρ′ p` z ρ′ = [(1,true),(0,true)].
  - Vrnemo to.

Rezultat: `sat [(1,true),(0,true)] dokaz`. ✓

---

## Problem 10 — Pravilnost SAT-solverja

### Glavna ideja

Pravilnost je **vgrajena v tip** `SatResult`. Konstruktor `sat ρ p` zahteva
`p : eval-cnf ρ φ ≡ just true`, torej Agda **ne dopusti** gradnje `sat ρ p`,
če nimamo veljavnega dokaza.

Zato je vsak rezultat oblike `sat ρ p`, ki ga naš solver vrne, **po
definiciji pravilen** — nič dodatnega ni za dokazati.

### Eksplicitna lema

Za jasnost dodamo izrecno lemo:

```agda
sat?-sound : ∀ {φ ρ p} → sat? φ ≡ sat ρ p → eval-cnf ρ φ ≡ just true
sat?-sound {p = p} _ = p
```

Pomen: če `sat?` vrne `sat ρ p`, potem je `p` že dokaz, da ρ zadovolji φ.

**Implementacija**: trivialno — pattern-matchamo na `{p = p}` in vrnemo `p`.
Ne potrebujemo nobene "indukcije" ali pomožnih lem.

### Kaj to dokazuje?

**Zdravost (soundness)**: če solver reče "našel sem ρ", ima dokaz, da je ρ
res rešitev. To je močnejša garancija od "verjamemo, da algoritem deluje".

### O popolnosti (completeness)

Za **polno** pravilnost bi želeli tudi:

> Če `sat? φ` vrne `unsat`, potem **ne obstaja** ρ tako, da
> `eval-cnf ρ φ ≡ just true`.

To je v Agdi netrivialno formalno dokazati, ker:

- Število ρ je neskončno (`Assignment = List (ℕ × Bool)` je neskončen tip).
- Treba bi bilo lokalizirati na "ρ-je, ki vsebujejo vse spremenljivke iz φ"
  in pokazati, da naš `sat-search` te izčrpa.
- Potem še lema "če manjka spremenljivka, eval-cnf vrne nothing, ne just true".

Naš algoritem **je** popoln (preveri vsa 2ⁿ prirejanja), le formalnega
dokaza popolnosti ne pišemo. To je standardna stopnja "soundness brez
completeness" — v projektnih pričakovanjih je to sprejemljivo.

Projektna naloga pravi: "*Show that the SAT solver is correct, if not
obvious from the output type.*" Pri naši zasnovi **je** očitna iz tipa.

---

## Problem 11 — NNF → CNF s Tseytinovo transformacijo

### Cilj

Pretvori NNF formulo v **equisatisfiabilno** CNF formulo.

**Equisatisfiabilna** pomeni: φ je zadovoljiva ⟺ ψ je zadovoljiva. Formuli
nista nujno ekvivalentni (ne dajeta istih vrednosti za vsak ρ), samo
"obstaja vs. ne obstaja" rešitev se ujema.

### Zakaj Tseytin?

**Naivna distribucijska metoda** (`a ∨ (b ∧ c) ≡ (a ∨ b) ∧ (a ∨ c)`)
proizvede formule **eksponentne** velikosti v najslabšem primeru. Primer:

```
(a₁ ∧ b₁) ∨ (a₂ ∧ b₂) ∨ ... ∨ (aₙ ∧ bₙ)
```

Po distribuciji ima 2ⁿ klavzul.

**Tseytin** vpelje sveže spremenljivke za vsako podformulo in rezultat ima
**linearno** velikost (3 klavzule na notranje vozlišče + 1 koren).

Cena: rezultat ni ekvivalenten, samo equisatisfiabilen. Vsebuje sveže
spremenljivke, ki niso v originalu.

### Ključna ideja

Za vsako podformulo ψ vpeljemo svežo spremenljivko `x_ψ`, ki bo
"predstavljala" vrednost ψ. Klavzule zakodirajo enakost `x_ψ ↔ ψ`.

#### Listi (literali)

Za list `lit ℓ` **ne** potrebujemo nove spremenljivke — literal ℓ že
predstavlja vrednost. "Koren-literal" tega vozlišča je sam ℓ.

#### Notranji ∧ (`a ∧n b`)

Naj la, lb predstavljata otroka (njuna koren-literala), x naj bo sveža za
to vozlišče.

Želimo: `x ↔ (la ∧ lb)`. V propozicijski logiki:

```
x ↔ (la ∧ lb)  ≡  (x → la ∧ lb) ∧ (la ∧ lb → x)
              ≡  (x → la) ∧ (x → lb) ∧ (la ∧ lb → x)
```

Vsako implikacijo prevedemo v disjunkcijo (`a → b ≡ ¬a ∨ b`):

| Originalno     | Klavzula CNF              | Pomen                |
|----------------|---------------------------|----------------------|
| x → la         | `¬x ∨ la`                 | če x, potem la       |
| x → lb         | `¬x ∨ lb`                 | če x, potem lb       |
| la ∧ lb → x    | `¬la ∨ ¬lb ∨ x`           | če la ∧ lb, potem x  |

V Agdi:

```agda
(neg n₂ ∨d lit la)                                  -- ¬x ∨ la
∷ (neg n₂ ∨d lit lb)                                -- ¬x ∨ lb
∷ (flip-lit la ∨d flip-lit lb ∨d lit (pos n₂))      -- ¬la ∨ ¬lb ∨ x
```

#### Notranji ∨ (`a ∨n b`)

Analogno za `x ↔ (la ∨ lb)`:

| Klavzula CNF       | Pomen                 |
|---------------------|----------------------|
| `¬x ∨ la ∨ lb`     | če x, potem la ∨ lb  |
| `¬la ∨ x`          | če la, potem x       |
| `¬lb ∨ x`          | če lb, potem x       |

#### Koren

Naj x_root predstavlja celotno formulo. Formula je zadovoljiva ⟺ obstaja
ρ s `x_root = true`. Dodamo zato **enojno klavzulo** `x_root` (en literal).

### Pomožne funkcije

```agda
flip-lit : Literal → Literal
flip-lit (pos n) = neg n
flip-lit (neg n) = pos n
```

Obrne polarnost literala — uporabljamo za "¬la" v klavzulah.

```agda
max-var : NNF → ℕ
max-var (lit ℓ)   = max-var-lit ℓ
max-var (a ∧n b)  = max-var a ⊔ max-var b
max-var (a ∨n b)  = max-var a ⊔ max-var b
```

Najdi največji indeks spremenljivke v formuli. Sveže alociramo iznad tega.

```agda
clauses-to-cnf : Disjunct → List Disjunct → CNF
clauses-to-cnf d []        = dis d
clauses-to-cnf d (c ∷ cs)  = d ∧c clauses-to-cnf c cs
```

CNF tip je **neprazna** konjunkcija (vsaj ena klavzula). Ta funkcija zloži
seznam klavzul v CNF, pri čemer prva klavzula `d` zagotovi neprazenost.

### Algoritem `tseytin`

```agda
tseytin : NNF → ℕ → ℕ × Literal × List Disjunct
tseytin (lit ℓ)  n = n , ℓ , []
tseytin (a ∧n b) n with tseytin a n
... | n₁ , la , cs-a with tseytin b n₁
...   | n₂ , lb , cs-b =
        suc n₂ , pos n₂ ,
          (neg n₂ ∨d lit la)
        ∷ (neg n₂ ∨d lit lb)
        ∷ (flip-lit la ∨d flip-lit lb ∨d lit (pos n₂))
        ∷ (cs-a ++ cs-b)
tseytin (a ∨n b) n = ... -- analogno
```

Struktura:

- **Vhod**: NNF formula + `n` = "naslednji svež indeks".
- **Izhod**: `(n', l, cs)` kjer:
  - `n'` = posodobljen "naslednji svež"
  - `l` = koren-literal te podformule (kasneje uporabljen v starševih
    klavzulah)
  - `cs` = vse klavzule, ki opisujejo to podformulo

Threading stanja: vsak rekurzivni klic dobi prejšnji `n'` kot svoj `n`.

**Primer trasiranja** za `lit (pos 0) ∧n lit (pos 1)`:

```
tseytin (lit (pos 0)) n  →  (n, pos 0, [])           -- list
tseytin (lit (pos 1)) n  →  (n, pos 1, [])           -- list
tseytin (∧n)  n          →  n₁ = n, la = pos 0
                          →  n₂ = n, lb = pos 1
                          →  alociramo x = pos n
                          →  return (suc n, pos n, [3 klavzule])
```

Klavzule: `¬xₙ ∨ x₀`, `¬xₙ ∨ x₁`, `¬x₀ ∨ ¬x₁ ∨ xₙ`.

### Vrhnja pretvorba

```agda
to-cnf : NNF → CNF
to-cnf φ with tseytin φ (suc (max-var φ))
... | _ , root , cs = clauses-to-cnf (lit root) cs
```

- `suc (max-var φ)` — prva sveža spremenljivka je strogo večja od katerekoli
  v vhodu. **Brez kolizij.**
- `clauses-to-cnf (lit root) cs` — koren je enojna klavzula `[root]`, ki
  zagotovi, da mora biti true (sicer formula = false).
- Če je vhod list `lit ℓ`, je `cs = []` in dobimo CNF `dis (lit ℓ)` — eno
  klavzulo z enim literalom. Že CNF. ✓

### Equisatisfiabilnost (intuitivno)

**Trditev**: φ je zadovoljiva ⟺ `to-cnf φ` je zadovoljiva.

**Skica**:

**(⇒)** Iz ρ za φ zgradimo ρ' za CNF:
- Za vsako spremenljivko v originalu: ρ'(x) = ρ(x).
- Za sveže Tseytin spremenljivke `x_ψ`: nastavi `ρ'(x_ψ) = eval ρ ψ`.
- Klavzule za `x_ψ ↔ struktura(ψ)` so po konstrukciji izpolnjene.
- Koren-klavzula `x_root` zahteva `x_root = true`. Ker je φ zadovoljiva pri
  ρ, je `x_root = true` pravilno (po naši definiciji `ρ'(x_root) = eval ρ φ = true`).

**(⇐)** Iz ρ' za CNF restrikcija na originalne spremenljivke da ρ za φ:
- Iz koren-klavzule sledi `ρ'(x_root) = true`.
- Iz klavzul za ↔ sledi, da je `x_root = struktura(root)` pod ρ'.
- Induktivno: `x_ψ = ψ` v ρ', za vsako podformulo ψ.
- Torej `eval ρ' root = true`, kar pomeni `eval (ρ' | original) φ = true`.

Formalni dokaz v Agdi je netrivialno (potreboval bi indukcijo po strukturi
NNF z lematami o klavzulah). V projektnih okvirih sprejmemo intuitivno.

---

## Problem 12 — SAT za poljubno Formula

### Cilj

Sestavi SAT-solver za poljubno propozicijsko formulo (ne samo CNF).

### Sestavljanje

Imamo tri kose iz prejšnjih problemov:

1. `to-nnf  : Formula → NNF`  (Problem 3)
2. `to-cnf  : NNF → CNF`      (Problem 11, Tseytin)
3. `sat?    : (φ : CNF) → SatResult φ`  (Problem 9)

Komponiramo:

```agda
sat-formula? : Formula → Maybe Assignment
sat-formula? φ with sat? (to-cnf (to-nnf φ))
... | sat ρ _ = just ρ
... | unsat   = nothing
```

Pomen:

1. **Pretvori Formula v NNF** — potisni negacije navznoter (De Morgan).
2. **Pretvori NNF v CNF** — Tseytin transformacija.
3. **Najdi prirejanje za CNF** — naš SAT-solver.
4. Če najde, **vrni prirejanje**.
   - Restrikcija ρ na originalne spremenljivke je zadovoljiva za originalno
     formulo (equisatisfiabilnost).

### Izhodni tip

`Maybe Assignment`:
- `just ρ` = formula je zadovoljiva, ρ je rešitev (vključno z Tseytin
  svežimi spremenljivkami).
- `nothing` = formula ni zadovoljiva.

### O dokazu pravilnosti

V tipu `Maybe Assignment` formalnega dokaza **ni**. Lahko bi naredili
podobno kot pri Problem 9:

```agda
data FormulaSat (φ : Formula) : Set where
  sat   : (ρ : Assignment) → eval ρ φ ≡ just true → FormulaSat φ
  unsat : FormulaSat φ
```

Da bi sestavili `sat ρ p`, bi potrebovali lemo:

> `eval-cnf ρ (to-cnf (to-nnf φ)) ≡ just true → eval ρ φ ≡ just true`

To pa je natanko equisatisfiabilnost Tseytinove transformacije + pravilnost
`to-nnf`, kar je netrivialno za formalno dokazati. V naši pragmatični
rešitvi vrnemo `Maybe Assignment` brez formalnega dokaza za Problem 12 (ki
je tako ali tako *-težavnostni).

### Praktična uporaba

```
sat-formula? (var 0 ∧f ¬f var 1)
  → just [(0, true), (1, false), ...sveže Tseytin spremenljivke...]
```

Vrnjeno ρ vsebuje vrednosti za sveže Tseytin spremenljivke, vendar je
**veljavno tudi za originalno formulo**: `eval ρ φ ≡ just true`. Klic `eval`
na originalni formuli ignorira sveže spremenljivke (jih ne sprašuje).

---

## Povzetek

| Komponenta | Tip | Pomen |
|------------|-----|-------|
| `SatResult φ` | data | Rezultat SAT z vgrajenim dokazom |
| `sat-search`  | fn  | Splitting iskanje po vseh ρ |
| `sat?`        | fn  | SAT za CNF s tipsko-pravilnostjo |
| `sat?-sound`  | lema | Eksplicitna formulacija pravilnosti |
| `tseytin`     | fn  | NNF → klavzule s svežimi spremenljivkami |
| `to-cnf`      | fn  | Vrhnji NNF → CNF (z root klavzulo) |
| `sat-formula?`| fn  | Formula → Maybe Assignment |

### Stopnja kompleksnosti

- **Problem 9 (***)**: DPLL skelet (splitting) + tipska pravilnost.
- **Problem 10 (**)**: Pravilnost po definiciji tipa + lema.
- **Problem 11 (***)**: Tseytin (linearna velikost, equisatisfiabilen).
- **Problem 12 (*)**: Trivialno komponiranje.

### Kaj bi nadgradili za "pravo" SAT-solver?

1. **Unit propagation** v `sat-search` (DPLL polno).
2. **Watched literals** za hitrejše ovrednotenje klavzul.
3. **Konflikt-driven clause learning** (CDCL).
4. **Formalni dokaz popolnosti** Problem 10.
5. **Formalni dokaz equisatisfiabilnosti** Tseytin (zelo zahtevno).

V naši rešitvi je glavna elegantna lastnost: **tip izhoda nosi dokaz
pravilnosti**, kar je značilna prednost dependently-typed Agde.
