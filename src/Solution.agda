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
-- Problem 9. SAT-solver za CNF (DPLL splitting rule)
------------------------------------------------------------
--
-- Algoritem: za vsako spremenljivko v formuli poskusimo najprej
-- true, nato false (splitting rule). Ko so vse spremenljivke
-- prirejene, ocenimo eval-cnf in vrnemo rezultat.
--
-- Pravilnost (Problem 10) je vgrajena v izhodni tip: konstruktor
-- `sat ρ p` nosi dokaz p : eval-cnf ρ φ ≡ just true.

-- Indeks spremenljivke literala
lit-var : Literal → ℕ
lit-var (pos n) = n
lit-var (neg n) = n

-- Indeksi spremenljivk v Disjunctu / CNF (z dvojniki)
dis-vars : Disjunct → List ℕ
dis-vars (lit ℓ)   = lit-var ℓ ∷ []
dis-vars (ℓ ∨d d)  = lit-var ℓ ∷ dis-vars d

cnf-vars : CNF → List ℕ
cnf-vars (dis d)   = dis-vars d
cnf-vars (d ∧c φ)  = dis-vars d ++ cnf-vars φ

-- Izhod SAT-solverja: zadovoljivo prirejanje + dokaz, ali unsat
data SatResult (φ : CNF) : Set where
  sat   : (ρ : Assignment) → eval-cnf ρ φ ≡ just true → SatResult φ
  unsat : SatResult φ

-- Splitting iskanje: poskusi true, potem false, vrni rezultat
sat-search : List ℕ → Assignment → (φ : CNF) → SatResult φ
sat-search []       ρ φ with eval-cnf ρ φ in eq
... | just true = sat ρ eq
... | _         = unsat
sat-search (v ∷ vs) ρ φ with sat-search vs (insert v true ρ) φ
... | sat ρ′ p = sat ρ′ p
... | unsat with sat-search vs (insert v false ρ) φ
...   | sat ρ′ p = sat ρ′ p
...   | unsat    = unsat

sat? : (φ : CNF) → SatResult φ
sat? φ = sat-search (cnf-vars φ) empty φ


------------------------------------------------------------
-- Problem 10. Pravilnost SAT-solverja
------------------------------------------------------------
--
-- Pravilnost je očitna iz izhodnega tipa: konstruktor `sat ρ p`
-- že zahteva dokaz `p : eval-cnf ρ φ ≡ just true`, zato je vsak
-- vrnjen `sat ρ p` po definiciji pravilna rešitev.
-- Spodnja lema to izrecno zapiše: če sat? vrne sat ρ p, potem
-- ρ res zadovolji φ.

sat?-sound : ∀ {φ ρ p} → sat? φ ≡ sat ρ p → eval-cnf ρ φ ≡ just true
sat?-sound {p = p} _ = p


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

-- Tseytin: vhod NNF + naslednji svež indeks
--   vrnemo: (nov next-fresh, koren-literal podformule, klavzule)
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

-- Vrhnja pretvorba: dodamo enojno klavzulo (koren = true)
to-cnf : NNF → CNF
to-cnf φ with tseytin φ (suc (max-var φ))
... | _ , root , cs = clauses-to-cnf (lit root) cs


------------------------------------------------------------
-- Problem 12. SAT-solver za poljubno Formula
------------------------------------------------------------
--
-- Sestavimo: Formula → NNF → CNF → SAT.
-- Tseytin pretvorba je equisatisfiabilna: če sat? najde
-- prirejanje za CNF, je restrikcija na originalne spremenljivke
-- tudi zadovoljivo prirejanje za originalno Formulo.

sat-formula? : Formula → Maybe Assignment
sat-formula? φ with sat? (to-cnf (to-nnf φ))
... | sat ρ _ = just ρ
... | unsat   = nothing
