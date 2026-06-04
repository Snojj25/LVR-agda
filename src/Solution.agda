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
  using (Dec; yes; no)
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
-- Problem 9. SAT-solver za CNF (DPLL)
--
-- na kratko: spremenljivke (kje prirejamo) → konflikt → pure literal → iskanje
-- φ ne spreminajmo!! samo ρ in rezemo veje ce je klavzula ze false
-- na koncu eval-cnf in eq gre v sat ρ eq (problem 10)

-- spremenljivke
lit-var : Literal → ℕ
lit-var (pos n) = n
lit-var (neg n) = n

dis-vars : Disjunct → List ℕ
dis-vars (lit ℓ)   = lit-var ℓ ∷ []
dis-vars (ℓ ∨d d)  = lit-var ℓ ∷ dis-vars d

cnf-vars : CNF → List ℕ
cnf-vars (dis d)   = dis-vars d
cnf-vars (d ∧c φ)  = dis-vars d ++ cnf-vars φ

-- konflikt / unit propagation (nekako)
lit-false? : Assignment → Literal → Bool
lit-false? ρ ℓ with eval-lit ρ ℓ
... | just false = true
... | _          = false

clause-conflict? : Assignment → Disjunct → Bool   -- vsi literali false?
clause-conflict? ρ (lit ℓ)  = lit-false? ρ ℓ
clause-conflict? ρ (ℓ ∨d d) = lit-false? ρ ℓ and clause-conflict? ρ d

cnf-conflict? : Assignment → CNF → Bool            -- katera koli klavzula?
cnf-conflict? ρ (dis d)  = clause-conflict? ρ d
cnf-conflict? ρ (d ∧c φ) = clause-conflict? ρ d or cnf-conflict? ρ φ

-- pure literal
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

pure-value : ℕ → CNF → Maybe Bool                  -- samo pos→true, samo neg→false
pure-value v φ with cnf-pos? v φ | cnf-neg? v φ
... | true  | false = just true
... | false | true  = just false
... | _     | _     = nothing

-- iskanje - splitting
data SatResult (φ : CNF) : Set where
  sat   : (ρ : Assignment) → eval-cnf ρ φ ≡ just true → SatResult φ
  unsat : SatResult φ

sat-search : List ℕ → Assignment → (φ : CNF) → SatResult φ
decide     : ℕ → List ℕ → Assignment → (φ : CNF) → SatResult φ
try-assign : ℕ → Bool → List ℕ → Assignment → (φ : CNF) → SatResult φ

sat-search []       ρ φ with eval-cnf ρ φ in eq
... | just true = sat ρ eq
... | _         = unsat
sat-search (v ∷ vs) ρ φ with lookup v ρ
... | just _  = sat-search vs ρ φ                  -- že prirejen → preskoči
... | nothing = decide v vs ρ φ

decide v vs ρ φ with pure-value v φ
... | just b  = try-assign v b vs ρ φ              -- pure → ena veja
... | nothing with try-assign v true vs ρ φ        -- sicer cepi: true, pa false
...   | sat ρ′ p = sat ρ′ p
...   | unsat    = try-assign v false vs ρ φ

try-assign v b vs ρ φ with cnf-conflict? (insert v b ρ) φ
... | true  = unsat                                -- konflikt → rez veje
... | false = sat-search vs (insert v b ρ) φ

sat? : (φ : CNF) → SatResult φ
sat? φ = sat-search (cnf-vars φ) empty φ


------------------------------------------------------------
-- Problem 10. Correctness of the SAT solver (soundness + completeness)
--
-- Pri tem problemu je vec komentarjev: moramo formalno razloziti soundness
-- in zakaj completeness v tej datoteki se ni dokazana do konca.

-- soundness -------------------------------------------------
-- Soundness: ce `sat? φ` vrne `sat ρ p`, potem ρ res zadovolij φ.
-- To sledi iz dizajna `SatResult` (Problem 9): konstruktor `sat` zahteva
--   p : eval-cnf ρ φ ≡ just true.
-- Na listu iskanja: `sat-search [] ρ φ with eval-cnf ρ φ in eq` → `sat ρ eq`.
-- Lema spodaj samo izlusci dokaz iz rezultata (za Problem 10 v porocilu).

sat?-sound : ∀ {φ ρ p} → sat? φ ≡ sat ρ p → eval-cnf ρ φ ≡ just true
sat?-sound {p = p} _ = p

-- completeness
--
-- Completeness pomeni: solver ne zamudi obstojece resitve in ne vrne unsat
--   ce model obstaja; ter ne laze z unsat ko modela ni.
--
-- Formalno (cilj, se ni dokazan v celoti v tej datoteki):
--   sat?-complete₁ : ∀ {φ ρ} → eval-cnf ρ φ ≡ just true
--                  → sat? φ ≡ sat ρ _
--   sat?-complete₂ : ∀ {φ} → (∀ ρ → eval-cnf ρ φ ≢ just true)
--                  → sat? φ ≡ unsat
--
-- Zakaj je to tezje kot soundness:
--   pri `sat ρ p` je dokaz p ze v konstruktorju. pri `unsat` tip `SatResult`
-- ne nosi dokaza "formula je res nezadovoljiva" — iz same definicije tipa
--   complete₂ ne mores dobiti brez dodatne argumentacije.
--
-- Za complete₁ bi bila glavna ideja: indukcija na `sat-search` / `decide` /
-- `try-assign`. Vsak korak DPLL bi zahteval svojo pod-lemo (insert + eval-cnf):
--   preskok v, ki je ze v ρ (dvojnik na cnf-vars)
--   pure literal — ohrani obstojeci satisfying assignment
--   zgodnji konflikt — nobena razsiritev ne more popraviti klavzule
--   cepitev — ce true veja ne uspe, obstaja resitev z v ↦ false
-- V okviru te naloge teh lem nismo razvili do konca.
--
-- Dodatno: `sat-search` obisce samo `cnf-vars φ`. Za completeness bi morali
-- dokazati da seznam pokrije vse indekse ki vplivajo na eval-cnf
-- (duplikati so ok, manjkajoci ne).
--
-- `Assignment` je delna lista — preverjene so le veje drevesa iskanja, ne pa
--   vseh moznih ρ v abstraktnem smislu.
--
-- Delni okvir indukcije (zapis za porocilo):
--   sat-search-complete :
--     ∀ vs ρ {φ} (p : eval-cnf ρ φ ≡ just true)
--     → sat-search vs ρ φ ≡ sat ρ _
--   bazni korak [] : iz p sledi `sat ρ eq`  — to deluje
--   korak (v ∷ vs) : razclenitev `lookup v ρ`
--      just _  → preskok (potrebna lema: enakovrednost ρ)
--      nothing → decide / try-assign  — tukaj se razcepi na pure, konflikt,
--                split; brez pomoznih lem o insert se dokaz ne zakljuci
--
-- `sat-from-proof` spodaj: ce ρ in dokaz p ze poznamo, zgradimo `SatResult`.
--   To je skladnost konstruktorja `sat` s tipom, ne completeness od `sat?`
--   (ne trdi da bo solver sam nasel ta ρ).

sat-from-proof : ∀ {φ} {ρ : Assignment} (p : eval-cnf ρ φ ≡ just true) → SatResult φ
sat-from-proof {ρ = ρ} p = sat ρ p


------------------------------------------------------------
-- Problem 11. NNF → CNF (Tseytin)
--
-- za vsako notranje vozlisce nova spremenljivka + 3 klavzule (and/or)
-- listi ostanejo literali, equisat ne dokazujemo

-- pomožno (flip-lit, max-var, ...)
flip-lit : Literal → Literal
flip-lit (pos n) = neg n
flip-lit (neg n) = pos n

max-var-lit : Literal → ℕ
max-var-lit (pos n) = n
max-var-lit (neg n) = n

max-var : NNF → ℕ
max-var (lit ℓ)   = max-var-lit ℓ
max-var (a ∧n b)  = max-var a ⊔ max-var b
max-var (a ∨n b)  = max-var a ⊔ max-var b

clauses-to-cnf : Disjunct → List Disjunct → CNF
clauses-to-cnf d []        = dis d
clauses-to-cnf d (c ∷ cs)  = d ∧c clauses-to-cnf c cs

-- tseytin - rekurzija
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
tseytin (a ∨n b) n with tseytin a n
... | n₁ , la , cs-a with tseytin b n₁
...   | n₂ , lb , cs-b =
        suc n₂ , pos n₂ ,
          (neg n₂ ∨d la ∨d lit lb)
        ∷ (flip-lit la ∨d lit (pos n₂))
        ∷ (flip-lit lb ∨d lit (pos n₂))
        ∷ (cs-a ++ cs-b)

-- to-cnf
to-cnf : NNF → CNF
to-cnf φ with tseytin φ (suc (max-var φ))
... | _ , root , cs = clauses-to-cnf (lit root) cs


------------------------------------------------------------
-- Problem 12. SAT za Formula
--
-- Formula → to-nnf → to-cnf → sat? → se enkrat eval na originalu
-- dokaz mora biti eval ρ φ ≡ just true (ne eval-cnf), tseyitina ne dokazujemo
-- zato ponovno preverimo ρ na formuli

-- FormulaSat tip
data FormulaSat (φ : Formula) : Set where
  sat   : (ρ : Assignment) → eval ρ φ ≡ just true → FormulaSat φ
  unsat : FormulaSat φ

-- sat-formula?
sat-formula? : (φ : Formula) → FormulaSat φ
sat-formula? φ with sat? (to-cnf (to-nnf φ))
... | unsat   = unsat
... | sat ρ _ with eval ρ φ in eq
...   | just true = sat ρ eq
...   | _         = unsat

-- sound + solve (brez dokaza v solve)
sat-formula?-sound : ∀ {φ ρ p} → sat-formula? φ ≡ sat ρ p → eval ρ φ ≡ just true
sat-formula?-sound {p = p} _ = p

solve : Formula → Maybe Assignment
solve φ with sat-formula? φ
... | sat ρ _ = just ρ
... | unsat   = nothing
