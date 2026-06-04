module Solution where

-- Imports

open import Data.Nat
  using (ℕ; _≟_; _⊔_; suc)
open import Data.Bool
  using (Bool; true; false; not)
  renaming (_∧_ to _and_; _∨_ to _or_)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.List
  using (List; []; _∷_; _++_)
open import Data.Product
  using (_×_; _,_)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty
  using (⊥)
open import Relation.Nullary
  using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

---------------------------------------------------------------------
-- Problem 1: Definiramo Formula type

data Formula : Set where
  var  : ℕ → Formula
  ¬f_  : Formula → Formula
  _∧f_ : Formula → Formula → Formula
  _∨f_ : Formula → Formula → Formula

infix  9 ¬f_
infixr 7 _∧f_
infixr 6 _∨f_

---------------------------------------------------------------------
-- Problem 2. Definramo literal, Iz tega sestavimo
-- definicijo NNF (Negation Normal Form)

data Literal : Set where
  pos : ℕ → Literal     
  neg : ℕ → Literal     

data NNF : Set where
  lit  : Literal → NNF
  _∧n_ : NNF → NNF → NNF
  _∨n_ : NNF → NNF → NNF

infixr 7 _∧n_
infixr 6 _∨n_

---------------------------------------------------------------------
-- Problem 3. Pretvorba Formula → NNF (to-nnf)
-- negacijo "potisnemo" navzdol z De Morganovimi zakoni
-- in ¬¬φ ≡ φ. ne pišemo ene velike to-nnf, ampak dve funkciji:
--   nnf⁺ φ  ≈  pretvori φ    nnf⁻ φ  ≈  pretvori ¬φ
-- Končna funkcija je to-nnf = nnf⁺.

nnf⁺ : Formula → NNF
nnf⁻ : Formula → NNF

nnf⁺ (var n)   = lit (pos n)
nnf⁺ (¬f φ)    = nnf⁻ φ
nnf⁺ (a ∧f b)  = nnf⁺ a ∧n nnf⁺ b
nnf⁺ (a ∨f b)  = nnf⁺ a ∨n nnf⁺ b

nnf⁻ (var n)   = lit (neg n)
nnf⁻ (¬f φ)    = nnf⁺ φ               -- dvojna negacija
nnf⁻ (a ∧f b)  = nnf⁻ a ∨n nnf⁻ b       -- De Morgan: ¬(a∧b)
nnf⁻ (a ∨f b)  = nnf⁻ a ∧n nnf⁻ b        -- De Morgan: ¬(a∨b)

to-nnf : Formula → NNF
to-nnf = nnf⁺

---------------------------------------------------------------------
-- Problem 4. 

infix 4 _∈ᴬ_

-- "rekurzivna definicija" za _∈ᴬ_ s pomočjo sum type 
-- (kaj pomeni biti v Listu (ℕ × Bool)?)
_∈ᴬ_ : ℕ → List (ℕ × Bool) → Set
k ∈ᴬ []               = ⊥
k ∈ᴬ ((k′ , _) ∷ kvs) = (k ≡ k′) ⊎ (k ∈ᴬ kvs)

-- Iz dokaza članstva preberi shranjen true/false
get : {k : ℕ} {kvs : List (ℕ × Bool)} → k ∈ᴬ kvs → Bool
get {kvs = []}              ()
get {kvs = (_ , v) ∷ _}     (inj₁ _) = v      -- najden na začetku
get {kvs = (_ , _) ∷ kvs}   (inj₂ p) = get p  -- najden v repu

-- Odloči članstvo in vrni dokaz (yes) ali dokaz da ni (no)
_∈ᴬ?_ : (k : ℕ) → (kvs : List (ℕ × Bool)) → Dec (k ∈ᴬ kvs)
k ∈ᴬ? []                = no λ ()
k ∈ᴬ? ((k′ , _) ∷ kvs)  with k ≟ k′
... | yes refl = yes (inj₁ refl)
... | no  k≢k′ with k ∈ᴬ? kvs
...   | yes p     = yes (inj₂ p)
...   | no  k∉kvs = no λ { (inj₁ p) → k≢k′ p
                         ; (inj₂ p) → k∉kvs p }

-- Assignment = seznam parov (številka spremenljivke, true/false)
Assignment : Set
Assignment = List (ℕ × Bool)

empty : Assignment
empty = []

-- lookup: če je k v ρ, just vrednost; sicer nothing
lookup : ℕ → Assignment → Maybe Bool
lookup k ρ with k ∈ᴬ? ρ
... | yes p = just (get p)
... | no  _ = nothing

-- insert: posodobi obstoječi ključ ali dodaj na konec
insert : ℕ → Bool → Assignment → Assignment
insert k v []                = (k , v) ∷ []
insert k v ((k′ , v′) ∷ ρ)   with k ≟ k′
... | yes _ = (k , v) ∷ ρ
... | no  _ = (k′ , v′) ∷ insert k v ρ

---------------------------------------------------------------------
-- Problem 5.  Evaluating a Formula

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


---------------------------------------------------------------------
-- Problem 6.  Evaluating an NNF

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


------------------------------------------------------------
-- Problem 7.  Definiramo Disjunct in CNF

data Disjunct : Set where
  lit  : Literal → Disjunct
  _∨d_ : Literal → Disjunct → Disjunct

data CNF : Set where
  dis  : Disjunct → CNF
  _∧c_ : Disjunct → CNF → CNF

infixr 6 _∨d_
infixr 7 _∧c_


------------------------------------------------------------
-- Problem 8.  eval-disjunct in eval-cnf


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


------------------------------------------------------------
-- Problem 9. SAT-solver za CNF — DPLL
------------------------------------------------------------
--
-- Klasični DPLL je sestavljen iz treh delov:
--   1) UNIT PROPAGATION  — če je v klavzuli en sam še nedoločen literal,
--                          vsi ostali pa že false, ga MORAMO nastaviti
--                          tako, da klavzulo zadovolji (sicer konflikt).
--   2) PURE LITERAL       — če se spremenljivka v formuli pojavi samo
--                          pozitivno (ali samo negativno), jo varno
--                          nastavimo na to vrednost (drugje ne škodi).
--   3) SPLITTING (cepitev) — sicer izberemo spremenljivko in poskusimo
--                          obe vrednosti (true, nato false).
--
-- POMEMBNO za naš dokaz: formule NE spreminjamo (φ ostane ista). Namesto
-- da bi iz klavzul brisali zadovoljene literale (kar dela "pravi" DPLL),
-- samo PAMETNO izbiramo vrednosti spremenljivk in ZGODAJ obrežemo veje,
-- ki vsebujejo že v celoti napačno (false) klavzulo. Posledica: na listu
-- iskanja še vedno samo pokličemo eval-cnf, zato dokaz pravilnosti
-- (Problem 10) ostane preprost — `sat ρ p` nosi p : eval-cnf ρ φ ≡ just true.

-- Indeks spremenljivke literala (pri pos/neg je to isti n)
lit-var : Literal → ℕ
lit-var (pos n) = n
lit-var (neg n) = n

-- Indeksi vseh spremenljivk v Disjunctu / CNF (lahko z dvojniki)
dis-vars : Disjunct → List ℕ
dis-vars (lit ℓ)   = lit-var ℓ ∷ []
dis-vars (ℓ ∨d d)  = lit-var ℓ ∷ dis-vars d

cnf-vars : CNF → List ℕ
cnf-vars (dis d)   = dis-vars d
cnf-vars (d ∧c φ)  = dis-vars d ++ cnf-vars φ

------------------------------------------------------------
-- (1) Zaznavanje konfliktov — osnova za unit propagation
------------------------------------------------------------
--
-- Unit propagation v jedru pomeni: "ne hodi po veji, kjer postane neka
-- klavzula v celoti false". Zato potrebujemo test, ali je klavzula (oz.
-- cela CNF) pod trenutnim ρ že napačna.

-- literal je "false", če ga ρ priredi in se ovrednoti v false
lit-false? : Assignment → Literal → Bool
lit-false? ρ ℓ with eval-lit ρ ℓ
... | just false = true
... | _          = false     -- true ali še nedoločen → ni (zanesljivo) false

-- klavzula je v KONFLIKTU, če so VSI njeni literali false
--   (takrat je ni mogoče več zadovoljiti — to je signal za rez veje)
clause-conflict? : Assignment → Disjunct → Bool
clause-conflict? ρ (lit ℓ)  = lit-false? ρ ℓ
clause-conflict? ρ (ℓ ∨d d) = lit-false? ρ ℓ and clause-conflict? ρ d

-- CNF je v konfliktu, če je v konfliktu KATERA KOLI klavzula
cnf-conflict? : Assignment → CNF → Bool
cnf-conflict? ρ (dis d)  = clause-conflict? ρ d
cnf-conflict? ρ (d ∧c φ) = clause-conflict? ρ d or cnf-conflict? ρ φ

------------------------------------------------------------
-- (2) Pure literal elimination
------------------------------------------------------------
--
-- Pogledamo, s kakšno polariteto se spremenljivka v sploh pojavlja v φ.

-- ali se v pojavi pozitivno (kot pos v) / negativno (kot neg v) v literalu
pos-occ? : ℕ → Literal → Bool
pos-occ? v (pos n) with v ≟ n
... | yes _ = true
... | no  _ = false
pos-occ? v (neg _) = false

neg-occ? : ℕ → Literal → Bool
neg-occ? v (neg n) with v ≟ n
... | yes _ = true
... | no  _ = false
neg-occ? v (pos _) = false

-- razširimo iskanje polaritete na klavzule in celoten CNF
dis-pos? : ℕ → Disjunct → Bool
dis-pos? v (lit ℓ)  = pos-occ? v ℓ
dis-pos? v (ℓ ∨d d) = pos-occ? v ℓ or dis-pos? v d

dis-neg? : ℕ → Disjunct → Bool
dis-neg? v (lit ℓ)  = neg-occ? v ℓ
dis-neg? v (ℓ ∨d d) = neg-occ? v ℓ or dis-neg? v d

cnf-pos? : ℕ → CNF → Bool
cnf-pos? v (dis d)  = dis-pos? v d
cnf-pos? v (d ∧c φ) = dis-pos? v d or cnf-pos? v φ

cnf-neg? : ℕ → CNF → Bool
cnf-neg? v (dis d)  = dis-neg? v d
cnf-neg? v (d ∧c φ) = dis-neg? v d or cnf-neg? v φ

-- pure literal: samo pozitivno → true; samo negativno → false;
--   mešano ali je sploh ni → nothing (ni pure, treba bo cepiti)
pure-value : ℕ → CNF → Maybe Bool
pure-value v φ with cnf-pos? v φ | cnf-neg? v φ
... | true  | false = just true
... | false | true  = just false
... | _     | _     = nothing

------------------------------------------------------------
-- (3) Iskanje s cepitvijo + zgornja dela vgrajena
------------------------------------------------------------

-- Izhod SAT-solverja: odvisni tip SatResult φ — sat ρ p vrne ρ + dokaz p,
data SatResult (φ : CNF) : Set where
  sat   : (ρ : Assignment) → eval-cnf ρ φ ≡ just true → SatResult φ
  unsat : SatResult φ

-- Tri medsebojno rekurzivne funkcije (najprej napovemo tipe):
--   sat-search — glavna zanka po seznamu spremenljivk
--   decide     — izbere strategijo (pure literal ali cepitev) za eno spr.
--   try-assign — priredi v←b, a najprej preveri konflikt (unit propagation)
sat-search : List ℕ → Assignment → (φ : CNF) → SatResult φ
decide     : ℕ → List ℕ → Assignment → (φ : CNF) → SatResult φ
try-assign : ℕ → Bool → List ℕ → Assignment → (φ : CNF) → SatResult φ

-- sat-search: ko zmanjka spremenljivk, ovrednotimo formulo (list iskanja).
sat-search []       ρ φ with eval-cnf ρ φ in eq
... | just true = sat ρ eq          -- eq je dokaz, ki ga zahteva `sat`
... | _         = unsat
-- sicer obdelamo prvo spremenljivko v
sat-search (v ∷ vs) ρ φ with lookup v ρ
... | just _  = sat-search vs ρ φ   -- v je že določen (dvojnik) → preskoči
... | nothing = decide v vs ρ φ     -- v je nov → izberi strategijo

-- decide: najprej poskusimo PURE LITERAL, sicer CEPIMO na obe vrednosti
decide v vs ρ φ with pure-value v φ
... | just b  = try-assign v b vs ρ φ              -- pure: dovolj ena vrednost
... | nothing with try-assign v true  vs ρ φ       -- cepitev: najprej true ...
...   | sat ρ′ p = sat ρ′ p
...   | unsat    = try-assign v false vs ρ φ        -- ... če ne gre, še false

-- try-assign: priredi v←b; če to TAKOJ naredi konflikt (neka klavzula je
--   v celoti false), je veja brezupna → unsat (to je učinek unit propagation:
--   napačna vrednost unit-klavzule je takoj zavrnjena). Sicer nadaljujemo.
try-assign v b vs ρ φ with cnf-conflict? (insert v b ρ) φ
... | true  = unsat
... | false = sat-search vs (insert v b ρ) φ

-- Vrhnji klic: prazno prirejanje + vse spremenljivke formule
sat? : (φ : CNF) → SatResult φ
sat? φ = sat-search (cnf-vars φ) empty φ


------------------------------------------------------------
-- Problem 10. Pravilnost SAT-solverja
------------------------------------------------------------
--
-- Pravilnost = zdravost + popolnost.
--   Zdravost:  če rečemo SAT, ρ res drži.
--   Popolnost: če obstaja ρ, ki drži, solver ga najde (ne vrne unsat).
--
-- (A) ZDRAVOST — očitna iz tipa `SatResult` + kratka lema spodaj.

sat?-sound : ∀ {φ ρ p} → sat? φ ≡ sat ρ p → eval-cnf ρ φ ≡ just true
sat?-sound {p = p} _ = p

-- (B) POPOLNOST — poskus (ni dokončan, datoteka se še vedno preveri)

-- Kaj bi radi dokazali (ena od oblik):
--
--   sat?-complete₁ : ∀ {φ ρ} → eval-cnf ρ φ ≡ just true
--                  → sat? φ ≡ sat ρ _
--
--   sat?-complete₂ : ∀ {φ} → (∀ ρ → eval-cnf ρ φ ≢ just true)
--                  → sat? φ ≡ unsat
--
-- Obe pomenita: solver ne zamudi prave rešitve in ne laže pri unsat.

-- Zakaj smo obtičali (kratek seznam):
--   1. `unsat` nima dokaza v tipu — Agda ne ve, da "res ni rešitve".
--   2. Dokaz bi bil velika indukcija na `sat-search` / `decide` / `try-assign`
--      (veliko primerov: pure literal, konflikt, cepitev, preskok dvojnika).
--   3. Morali bi dokazati, da `cnf-vars φ` vsebuje vse spremenljivke, ki
--      vplivajo na `eval-cnf` (duplikati so OK, manjkajoči indeks pa ne).
--   4. `Assignment` je delna lista — težko povezati "preverili smo vse veje
--      iskanja" z "za vsak ρ v univerzu".

-- Okvir indukcije (samo na papirju — z luknjami, ne v živo kodi):
--
--   sat?-complete : ∀ {φ ρ} (p : eval-cnf ρ φ ≡ just true) → sat? φ ≡ sat ρ _
--   sat-search-complete : ∀ vs ρ {φ} (p : ...) → sat-search vs ρ φ ≡ sat ρ _
--   bazni [] : sat ρ p
--   korak (v ∷ vs): indukcija + insert true/false + pure-value + konflikt  ← tukaj obtičamo

-- Kar smo uspeli brez indukcije: iz danega dokaza p ročno zgradimo `SatResult`
-- (to NI popolnost solverja — samo pove, da konstruktor `sat` ustreza tipu).
sat-from-proof : ∀ {φ} {ρ : Assignment} (p : eval-cnf ρ φ ≡ just true) → SatResult φ
sat-from-proof {ρ = ρ} p = sat ρ p


------------------------------------------------------------
-- Problem 11. NNF → CNF s Tseytinovo transformacijo
------------------------------------------------------------
--
-- Za vsako notranje vozlišče vpeljemo svežo spremenljivko x_i in
-- dodamo klavzule, ki kodirajo x_i ↔ (struktura vozlišča). Listi
-- (literali) ne potrebujejo svežih spremenljivk. Rezultat ima
-- linearno število klavzul (3 na notranje vozlišče) in je
-- equisatisfiabilen z vhodom.

-- Obrat literala
flip-lit : Literal → Literal
flip-lit (pos n) = neg n
flip-lit (neg n) = pos n

-- Najvišji indeks spremenljivke v NNF (sveže alociramo iznad)
max-var-lit : Literal → ℕ
max-var-lit (pos n) = n
max-var-lit (neg n) = n

max-var : NNF → ℕ
max-var (lit ℓ)   = max-var-lit ℓ
max-var (a ∧n b)  = max-var a ⊔ max-var b
max-var (a ∨n b)  = max-var a ⊔ max-var b

-- Seznam klavzul + obvezna prva → CNF
clauses-to-cnf : Disjunct → List Disjunct → CNF
clauses-to-cnf d []        = dis d
clauses-to-cnf d (c ∷ cs)  = d ∧c clauses-to-cnf c cs

-- Tseytin:
tseytin : NNF → ℕ → ℕ × Literal × List Disjunct
-- list: literal že "predstavlja" sam sebe, brez svežih spremenljivk
tseytin (lit ℓ)  n = n , ℓ , []
-- x ↔ (la ∧ lb):  (x→la) ∧ (x→lb) ∧ (la∧lb→x)
tseytin (a ∧n b) n with tseytin a n
... | n₁ , la , cs-a with tseytin b n₁
...   | n₂ , lb , cs-b =
        suc n₂ , pos n₂ ,
          (neg n₂ ∨d lit la)                            -- ¬x ∨ la      (x → la)
        ∷ (neg n₂ ∨d lit lb)                            -- ¬x ∨ lb      (x → lb)
        ∷ (flip-lit la ∨d flip-lit lb ∨d lit (pos n₂))  -- ¬la∨¬lb∨x    (la∧lb → x)
        ∷ (cs-a ++ cs-b)

-- x ↔ (la ∨ lb):  (x→la∨lb) ∧ (la→x) ∧ (lb→x)
tseytin (a ∨n b) n with tseytin a n
... | n₁ , la , cs-a with tseytin b n₁
...   | n₂ , lb , cs-b =
        suc n₂ , pos n₂ ,
          (neg n₂ ∨d la ∨d lit lb)                      -- ¬x ∨ la ∨ lb (x → la∨lb)
        ∷ (flip-lit la ∨d lit (pos n₂))                 -- ¬la ∨ x      (la → x)
        ∷ (flip-lit lb ∨d lit (pos n₂))                 -- ¬lb ∨ x      (lb → x)
        ∷ (cs-a ++ cs-b)

to-cnf : NNF → CNF
to-cnf φ with tseytin φ (suc (max-var φ))
... | _ , root , cs = clauses-to-cnf (lit root) cs


------------------------------------------------------------
-- Problem 12. SAT-solver za poljubno Formula
------------------------------------------------------------
--
-- Sestavimo cevovod:  Formula → NNF → CNF → SAT.
--
-- Tudi tu hočemo rezultat z DOKAZOM (kot pri Problem 9), a tokrat
-- mora dokaz govoriti o `eval` na ORIGINALNI Formuli — ne o CNF.
-- Tseytinove pravilnosti formalno ne dokazujemo (težko!), zato
-- uporabimo isti trik kot pri SAT-solverju: kandidatno prirejanje ρ
-- iz CNF-solverja še enkrat PREVERIMO z `eval ρ φ` na originalni
-- formuli in šele ob `just true` vrnemo `sat ρ` z dokazom.
-- Tako je rezultat ZDRAV po konstrukciji, brez dokazovanja Tseytina.

-- Izhod za poljubno formulo: dokaz govori o eval na Formula
data FormulaSat (φ : Formula) : Set where
  sat   : (ρ : Assignment) → eval ρ φ ≡ just true → FormulaSat φ
  unsat : FormulaSat φ

sat-formula? : (φ : Formula) → FormulaSat φ
sat-formula? φ with sat? (to-cnf (to-nnf φ))
... | unsat   = unsat                       -- CNF nezadovoljiv → tudi Formula
... | sat ρ _ with eval ρ φ in eq           -- ponovno preverimo na Formuli
...   | just true = sat ρ eq                -- eq : eval ρ φ ≡ just true
...   | _         = unsat

-- Pravilnost Problem 12 (spet očitna iz tipa): če sat-formula? vrne
-- `sat ρ p`, potem ρ res zadovolji originalno formulo φ.
sat-formula?-sound : ∀ {φ ρ p} → sat-formula? φ ≡ sat ρ p → eval ρ φ ≡ just true
sat-formula?-sound {p = p} _ = p

-- Priročna oblika, ki vrne le prirejanje (brez dokaza)
solve : Formula → Maybe Assignment
solve φ with sat-formula? φ
... | sat ρ _ = just ρ
... | unsat   = nothing
