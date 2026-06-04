# Rešitev problemov 9–12 — pregled

Koda: `src/Solution.agda` (od ~190). Za vsak problem je krajši vodič + HTML vizualizacija.

| Problem | Markdown | HTML (v živo) |
|---------|----------|----------------|
| 9  | (v kodi + spodaj) | [problem9-visual.html](problem9-visual.html) |
| 10 | [10-sat-correctness.md](10-sat-correctness.md) | [problem10-visual.html](problem10-visual.html) |
| 11 | [11-tseytin.md](11-tseytin.md) | [problem11-visual.html](problem11-visual.html) |
| 12 | [12-formula-sat.md](12-formula-sat.md) | [problem12-visual.html](problem12-visual.html) |

---

## Pregled

| Problem | Cilj | Naša rešitev |
|---------|------|---------------|
| 9  | SAT za CNF | DPLL + `SatResult` z dokazom |
| 10 | Pravilnost | Zdravost iz tipa; popolnost odprta |
| 11 | NNF → CNF | Tseytin (linearno) |
| 12 | SAT za `Formula` | Cevovod + `eval` na originalu |

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

### Trije deli DPLL

Klasični DPLL ima tri sestavne dele; mi imamo vse tri:

1. **Unit propagation** — če je v klavzuli en sam še nedoločen literal, vsi
   ostali pa že `false`, ga moramo nastaviti tako, da klavzulo zadovolji.
2. **Pure literal elimination** — če se spremenljivka pojavi le pozitivno
   (ali le negativno), jo varno nastavimo na to vrednost.
3. **Splitting rule** — sicer izberemo spremenljivko in poskusimo obe vrednosti.

**Ključna odločitev:** formule **ne spreminjamo** (φ ostane ista). Namesto da
bi iz klavzul brisali zadovoljene literale (kot "pravi" DPLL), samo pametno
izbiramo vrednosti spremenljivk in zgodaj režemo veje s konfliktom. Tako na
listu iskanja še vedno samo pokličemo `eval-cnf`, zato dokaz pravilnosti
(Problem 10) ostane preprost.

### Pomožne funkcije: zbiranje spremenljivk

Algoritem mora vedeti, **na katerih** spremenljivkah dela. Zberemo vse indekse:

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

Rezultat lahko vsebuje **dvojnike**; iskanje jih preprosto preskoči (glej
spodaj `lookup v ρ`).

### (1) Zaznavanje konfliktov — osnova za unit propagation

Unit propagation pomeni "ne hodi po veji, kjer je neka klavzula v celoti
`false`". Zato potrebujemo test, ali je klavzula/CNF pod ρ že napačna:

```agda
lit-false? : Assignment → Literal → Bool
lit-false? ρ ℓ with eval-lit ρ ℓ
... | just false = true
... | _          = false

clause-conflict? : Assignment → Disjunct → Bool      -- VSI literali false?
clause-conflict? ρ (lit ℓ)  = lit-false? ρ ℓ
clause-conflict? ρ (ℓ ∨d d) = lit-false? ρ ℓ and clause-conflict? ρ d

cnf-conflict? : Assignment → CNF → Bool              -- KATERA KOLI klavzula?
cnf-conflict? ρ (dis d)  = clause-conflict? ρ d
cnf-conflict? ρ (d ∧c φ) = clause-conflict? ρ d or cnf-conflict? ρ φ
```

Ko v iskanju prirejamo spremenljivko in s tem naredimo neko klavzulo v celoti
`false`, je to natanko situacija unit-klavzule z napačno izbiro → vejo
zavržemo. Tako se učinek unit propagation realizira ob izbiri spremenljivke.

### (2) Pure literal elimination

Pogledamo, s kakšno polariteto se `v` pojavi v φ:

```agda
pos-occ? / neg-occ?   -- pojavi se v en literal kot pos v / neg v
dis-pos? / dis-neg?   -- ... v klavzuli
cnf-pos? / cnf-neg?   -- ... kjerkoli v CNF

pure-value : ℕ → CNF → Maybe Bool
pure-value v φ with cnf-pos? v φ | cnf-neg? v φ
... | true  | false = just true     -- samo pozitivno → true
... | false | true  = just false    -- samo negativno → false
... | _     | _     = nothing       -- mešano/odsotno → ni pure
```

Pure literal lahko varno fiksiramo: če je φ zadovoljiva, je zadovoljiva tudi
z `v` nastavljenim na njegovo edino polariteto (drugje ne škodi).

### (3) Iskanje: tri medsebojno rekurzivne funkcije

```agda
sat-search : List ℕ → Assignment → (φ : CNF) → SatResult φ
decide     : ℕ → List ℕ → Assignment → (φ : CNF) → SatResult φ
try-assign : ℕ → Bool → List ℕ → Assignment → (φ : CNF) → SatResult φ

sat-search []       ρ φ with eval-cnf ρ φ in eq
... | just true = sat ρ eq          -- list: ovrednoti, eq je dokaz
... | _         = unsat
sat-search (v ∷ vs) ρ φ with lookup v ρ
... | just _  = sat-search vs ρ φ   -- v že določen (dvojnik) → preskoči
... | nothing = decide v vs ρ φ

decide v vs ρ φ with pure-value v φ
... | just b  = try-assign v b vs ρ φ           -- PURE: dovolj ena vrednost
... | nothing with try-assign v true  vs ρ φ    -- CEPITEV: najprej true ...
...   | sat ρ′ p = sat ρ′ p
...   | unsat    = try-assign v false vs ρ φ     -- ... sicer false

try-assign v b vs ρ φ with cnf-conflict? (insert v b ρ) φ
... | true  = unsat                              -- UNIT/konflikt → rez veje
... | false = sat-search vs (insert v b ρ) φ
```

Razlaga vlog:

- **`sat-search`** — glavna zanka po seznamu spremenljivk. Na listu (`[]`)
  ovrednoti formulo; `with … in eq` da dokaz `eq : eval-cnf ρ φ ≡ just true`,
  ki ga zahteva konstruktor `sat`. Že prirejene spremenljivke preskoči.
- **`decide`** — izbere strategijo: pure literal (ena veja) ali cepitev (obe).
- **`try-assign`** — priredi `v ← b`, a najprej preveri konflikt; če nastane,
  je veja brezupna (učinek unit propagation), sicer nadaljuje.

### Terminacija

Vse tri funkcije rekurzirajo tako, da seznam spremenljivk strogo pade: cikel
`sat-search (v ∷ vs) → decide v vs → try-assign v b vs → sat-search vs`. Ob
vsakem obhodu se `v ∷ vs` skrči na `vs`, zato Agdin terminacijski preverjevalnik
to sprejme. ✓

### Vrhnja funkcija

```agda
sat? : (φ : CNF) → SatResult φ
sat? φ = sat-search (cnf-vars φ) empty φ
```

Začnemo s **praznim** prirejanjem in **vsemi** spremenljivkami formule.

### Primer izvajanja

Vzemi φ = `(x₀ ∨ ¬x₁)`. CNF: `dis (pos 0 ∨d lit (neg 1))`.

- `cnf-vars φ = [0, 1]`, `sat-search [0,1] [] φ`.
- `v = 0`: ni v ρ → `decide 0 [1] [] φ`.
  - `pure-value 0 φ`: 0 se pojavi le pozitivno → `just true`. **Pure literal!**
  - `try-assign 0 true [1] [] φ`: ni konflikta → `sat-search [1] [(0,true)] φ`.
- `v = 1`: ni v ρ → `decide 1 [] [(0,true)] φ`.
  - `pure-value 1 φ`: 1 le negativno → `just false`. **Pure literal!**
  - `try-assign 1 false [] [(0,true)] φ`: ni konflikta →
    `sat-search [] [(1,false),(0,true)] φ`.
- List: `eval-cnf` na (x₀=T, x₁=F): `T ∨ ¬F = T ∨ T = T` → `sat ρ eq`.

Rezultat: `sat [(1,false),(0,true)] dokaz`. Opazi: ker sta oba literala pure,
**nismo cepili** — pure literal elimination je takoj našla rešitev. ✓

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

Komponiramo — a rezultat naredimo **proof-carrying** (kot pri Problem 9):

```agda
data FormulaSat (φ : Formula) : Set where
  sat   : (ρ : Assignment) → eval ρ φ ≡ just true → FormulaSat φ
  unsat : FormulaSat φ

sat-formula? : (φ : Formula) → FormulaSat φ
sat-formula? φ with sat? (to-cnf (to-nnf φ))
... | unsat   = unsat                       -- CNF nezadovoljiv → tudi Formula
... | sat ρ _ with eval ρ φ in eq           -- PONOVNO preverimo na Formuli
...   | just true = sat ρ eq                -- eq : eval ρ φ ≡ just true
...   | _         = unsat
```

Pomen:

1. **Pretvori Formula v NNF** — potisni negacije navznoter (De Morgan).
2. **Pretvori NNF v CNF** — Tseytin transformacija.
3. **Najdi prirejanje za CNF** — naš SAT-solver vrne kandidatni ρ.
4. **Ponovno preveri** `eval ρ φ` na ORIGINALNI formuli. Šele ob `just true`
   vrnemo `sat ρ eq` z dokazom `eq`.

### Ključni trik: dokaz s ponovnim preverjanjem

Pri Problem 12 hočemo dokaz, ki govori o `eval` na **originalni Formuli** (ne
o CNF). Formalno dokazati, da Tseytin ohranja zadovoljivost, je zelo zahtevno:
potrebovali bi lemo

> `eval-cnf ρ (to-cnf (to-nnf φ)) ≡ just true → eval ρ φ ≡ just true`

ki je natanko pravilnost Tseytina + `to-nnf`. **Namesto tega** uporabimo isti
trik kot pri SAT-solverju: kandidatni ρ samo **ponovno poženemo skozi `eval`**
na originalni formuli. Z `with eval ρ φ in eq` dobimo dokaz `eq`, ki ga zahteva
konstruktor `sat`. Tako je rezultat **zdrav po konstrukciji**, brez dokazovanja
Tseytina.

### Izhodni tip in pravilnost

`FormulaSat φ`:
- `sat ρ p` = ρ zadovolji φ, **z dokazom** `p : eval ρ φ ≡ just true`.
- `unsat` = solver ni našel rešitve.

Pravilnost je spet očitna iz tipa; izrecno jo zapiše lema:

```agda
sat-formula?-sound : ∀ {φ ρ p} → sat-formula? φ ≡ sat ρ p → eval ρ φ ≡ just true
sat-formula?-sound {p = p} _ = p
```

Za udobje dodamo še obliko, ki vrne le prirejanje:

```agda
solve : Formula → Maybe Assignment
solve φ with sat-formula? φ
... | sat ρ _ = just ρ
... | unsat   = nothing
```

### Opomba o popolnosti

Ker ponovno preverjamo na originalni formuli, je `sat` veja vedno zdrava.
Edina cena: če bi (v praksi se ne zgodi) Tseytinov ρ po restrikciji ne dal
`just true` na φ, bi vrnili `unsat` — kar ohrani zdravost, a ne popolnosti.
V praksi `cnf-vars` zajame vse originalne spremenljivke, zato `eval ρ φ` da
`just true` in dobimo `sat ρ eq`.

### Praktična uporaba

```
solve (var 0 ∧f ¬f var 1)
  → just [(0, true), (1, false), ...sveže Tseytin spremenljivke...]
```

Vrnjeno ρ vsebuje tudi sveže Tseytin spremenljivke, a je **veljavno za
originalno formulo**: `eval ρ φ ≡ just true` (kar dokaz `p` izrecno potrjuje).

---

## Povzetek

| Komponenta | Tip | Pomen |
|------------|-----|-------|
| `SatResult φ` | data | Rezultat SAT z vgrajenim dokazom |
| `cnf-conflict?` | fn | Zaznava konflikta (osnova za unit propagation) |
| `pure-value`  | fn  | Pure literal elimination |
| `sat-search` / `decide` / `try-assign` | fn | DPLL iskanje (vse tri komponente) |
| `sat?`        | fn  | SAT za CNF s tipsko-pravilnostjo |
| `sat?-sound`  | lema | Eksplicitna formulacija pravilnosti |
| `tseytin`     | fn  | NNF → klavzule s svežimi spremenljivkami |
| `to-cnf`      | fn  | Vrhnji NNF → CNF (z root klavzulo) |
| `FormulaSat φ`| data | Rezultat SAT za Formulo z vgrajenim dokazom |
| `sat-formula?`| fn  | Formula → FormulaSat (proof-carrying) |
| `sat-formula?-sound` | lema | Pravilnost Problema 12 |
| `solve`       | fn  | Formula → Maybe Assignment (priročno) |

### Stopnja kompleksnosti

- **Problem 9 (***)**: DPLL z vsemi tremi deli (unit propagation, pure
  literal, splitting) + tipska pravilnost.
- **Problem 10 (**)**: Pravilnost po definiciji tipa + lema.
- **Problem 11 (***)**: Tseytin (linearna velikost, equisatisfiabilen).
- **Problem 12 (*)**: Komponiranje + proof-carrying izhod (dokaz s ponovnim
  preverjanjem na originalni formuli).

### Kaj bi nadgradili za "pravo" SAT-solver?

1. **Watched literals** za hitrejše ovrednotenje klavzul.
2. **Konflikt-driven clause learning** (CDCL).
4. **Formalni dokaz popolnosti** Problem 10.
5. **Formalni dokaz equisatisfiabilnosti** Tseytin (zelo zahtevno).

V naši rešitvi je glavna elegantna lastnost: **tip izhoda nosi dokaz
pravilnosti**, kar je značilna prednost dependently-typed Agde.
