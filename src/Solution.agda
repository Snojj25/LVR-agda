module Solution where

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


-- Problem 1: tip Formula

data Formula : Set where
  var  : ℕ → Formula
  ¬f_  : Formula → Formula
  _∧f_ : Formula → Formula → Formula
  _∨f_ : Formula → Formula → Formula

infix  9 ¬f_
infixr 7 _∧f_
infixr 6 _∨f_


-- Problem 2: literali in NNF

data Literal : Set where
  pos : ℕ → Literal
  neg : ℕ → Literal

data NNF : Set where
  lit  : Literal → NNF
  _∧n_ : NNF → NNF → NNF
  _∨n_ : NNF → NNF → NNF

infixr 7 _∧n_
infixr 6 _∨n_


-- Problem 3: pretvorba Formula → NNF
--
-- Negacijo potiskamo navzdol z De Morganom in ¬¬φ = φ. Namesto ene velike
-- funkcije sta dve vzajemno rekurzivni: nnf⁺ prevede φ, nnf⁻ prevede ¬φ.

nnf⁺ : Formula → NNF
nnf⁻ : Formula → NNF

nnf⁺ (var n)  = lit (pos n)
nnf⁺ (¬f φ)   = nnf⁻ φ
nnf⁺ (a ∧f b) = nnf⁺ a ∧n nnf⁺ b
nnf⁺ (a ∨f b) = nnf⁺ a ∨n nnf⁺ b

nnf⁻ (var n)  = lit (neg n)
nnf⁻ (¬f φ)   = nnf⁺ φ   -- dvojna negacija
nnf⁻ (a ∧f b) = nnf⁻ a ∨n nnf⁻ b   -- De Morgan
nnf⁻ (a ∨f b) = nnf⁻ a ∧n nnf⁻ b

to-nnf : Formula → NNF
to-nnf = nnf⁺


-- Problem 4: prirejanja (Assignment)
--
-- Prirejanje je preprosto seznam parov (spremenljivka, vrednost). Članstvo
-- ključa definiramo rekurzivno kot Set, da lahko iz dokaza članstva potem
-- preberemo shranjeno vrednost.

infix 4 _∈ᴬ_

_∈ᴬ_ : ℕ → List (ℕ × Bool) → Set
k ∈ᴬ []               = ⊥
k ∈ᴬ ((k′ , _) ∷ kvs) = (k ≡ k′) ⊎ (k ∈ᴬ kvs)

get : {k : ℕ} {kvs : List (ℕ × Bool)} → k ∈ᴬ kvs → Bool
get {kvs = []} ()
get {kvs = (_ , v) ∷ _}   (inj₁ _) = v
get {kvs = (_ , _) ∷ kvs} (inj₂ p) = get p

_∈ᴬ?_ : (k : ℕ) → (kvs : List (ℕ × Bool)) → Dec (k ∈ᴬ kvs)
k ∈ᴬ? []                = no λ ()
k ∈ᴬ? ((k′ , _) ∷ kvs)  with k ≟ k′
... | yes refl = yes (inj₁ refl)
... | no  k≢k′ with k ∈ᴬ? kvs
...   | yes p     = yes (inj₂ p)
...   | no  k∉kvs = no λ { (inj₁ p) → k≢k′ p
                         ; (inj₂ p) → k∉kvs p }

Assignment : Set
Assignment = List (ℕ × Bool)

empty : Assignment
empty = []

lookup : ℕ → Assignment → Maybe Bool
lookup k ρ with k ∈ᴬ? ρ
... | yes p = just (get p)
... | no  _ = nothing

-- posodobi obstoječi ključ ali dodaj na konec
insert : ℕ → Bool → Assignment → Assignment
insert k v []                = (k , v) ∷ []
insert k v ((k′ , v′) ∷ ρ)   with k ≟ k′
... | yes _ = (k , v) ∷ ρ
... | no  _ = (k′ , v′) ∷ insert k v ρ


-- Problem 5: evalvacija formule
--
-- nothing pomeni, da kakšna spremenljivka manjka v ρ.

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


-- Problem 6: evalvacija NNF

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


-- Problem 7: Disjunct in CNF

data Disjunct : Set where
  lit  : Literal → Disjunct
  _∨d_ : Literal → Disjunct → Disjunct

data CNF : Set where
  dis  : Disjunct → CNF
  _∧c_ : Disjunct → CNF → CNF

infixr 6 _∨d_
infixr 7 _∧c_


-- Problem 8: eval-disjunct in eval-cnf

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
-- Problem 9: SAT solver za CNF (DPLL)
--
-- Formule ne preoblikujemo, samo dograjujemo ρ in režemo veje, na katerih
-- je kakšna klavzula že v celoti false. Na listu iskanja potem eval-cnf
-- sam vrne dokaz za konstruktor sat.

lit-var : Literal → ℕ
lit-var (pos n) = n
lit-var (neg n) = n

dis-vars : Disjunct → List ℕ
dis-vars (lit ℓ)   = lit-var ℓ ∷ []
dis-vars (ℓ ∨d d)  = lit-var ℓ ∷ dis-vars d

cnf-vars : CNF → List ℕ
cnf-vars (dis d)   = dis-vars d
cnf-vars (d ∧c φ)  = dis-vars d ++ cnf-vars φ

-- klavzula je konfliktna, ko so vsi njeni literali false pod ρ
lit-false? : Assignment → Literal → Bool
lit-false? ρ ℓ with eval-lit ρ ℓ
... | just false = true
... | _          = false

clause-conflict? : Assignment → Disjunct → Bool
clause-conflict? ρ (lit ℓ)  = lit-false? ρ ℓ
clause-conflict? ρ (ℓ ∨d d) = lit-false? ρ ℓ and clause-conflict? ρ d

cnf-conflict? : Assignment → CNF → Bool
cnf-conflict? ρ (dis d)  = clause-conflict? ρ d
cnf-conflict? ρ (d ∧c φ) = clause-conflict? ρ d or cnf-conflict? ρ φ

-- pure literal: spremenljivka, ki se pojavlja samo z eno polariteto,
-- lahko takoj dobi ustrezno vrednost (ni se treba cepiti)

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

pure-value : ℕ → CNF → Maybe Bool
pure-value v φ with cnf-pos? v φ | cnf-neg? v φ
... | true  | false = just true
... | false | true  = just false
... | _     | _     = nothing

-- samo iskanje: sat-search gre po seznamu spremenljivk, decide se odloči
-- kako prirediti naslednjo, try-assign preveri konflikt in nadaljuje

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
... | just _  = sat-search vs ρ φ   -- v je že prirejen (dvojnik v cnf-vars)
... | nothing = decide v vs ρ φ

decide v vs ρ φ with pure-value v φ
... | just b  = try-assign v b vs ρ φ
... | nothing with try-assign v true vs ρ φ
...   | sat ρ′ p = sat ρ′ p
...   | unsat    = try-assign v false vs ρ φ

try-assign v b vs ρ φ with cnf-conflict? (insert v b ρ) φ
... | true  = unsat
... | false = sat-search vs (insert v b ρ) φ

sat? : (φ : CNF) → SatResult φ
sat? φ = sat-search (cnf-vars φ) empty φ


------------------------------------------------------------
-- Problem 10: pravilnost SAT solverja
--
-- Zdravost je tu praktično zastonj: konstruktor sat že zahteva dokaz
-- eval-cnf ρ φ ≡ just true (na listu iskanja ga dobimo iz `with ... in eq`),
-- tako da ga samo izvlečemo iz rezultata.

sat?-sound : ∀ {φ ρ p} → sat? φ ≡ sat ρ p → eval-cnf ρ φ ≡ just true
sat?-sound {p = p} _ = p

-- Popolnost bi se glasila nekako takole:
--
--   sat?-complete₁ : ∀ {φ ρ} → eval-cnf ρ φ ≡ just true → sat? φ ≡ sat ρ _
--   sat?-complete₂ : ∀ {φ} → (∀ ρ → eval-cnf ρ φ ≢ just true) → sat? φ ≡ unsat
--
-- ampak tega nisem dokazal. Prva ovira je že sam tip SatResult: unsat ne
-- nosi nobenega dokaza, torej iz definicije ne sledi "za vse ρ formula ni
-- resnična" — druge smeri se sploh ne da izpeljati brez spremembe tipa.
--
-- Prva smer bi bila velika indukcija po sat-search / decide / try-assign:
-- za vsak korak DPLL pokazati, da veja ne izgubi rešitve, ki razširja
-- trenutni delni ρ. Težavni koraki: preskok že prirejene spremenljivke,
-- pure literal (ali res ne uniči kakšne rešitve?), rez ob konfliktu in
-- cepitev (če true ne uspe, mora rešitev obstajati s false). Vsak od teh
-- primerov potrebuje svoje leme o eval-cnf in insert, indukcija pa se brez
-- njih ne zaključi.
--
-- Poleg tega iskanje obišče samo spremenljivke iz cnf-vars φ, torej bi
-- morali dokazati še, da na tem seznamu nobena relevantna ne manjka.
-- In ker je Assignment delen (lookup lahko vrne nothing), "preverili smo
-- vse veje iskanja" ni očitno isto kot "za vsak ρ v matematičnem smislu".
--
-- Kar pa je lahko: če ρ in dokaz p že imaš, lahko SatResult sestaviš ročno.
-- To ni popolnost solverja (nič ne pravi, da bo sat? ta ρ našel), samo
-- konstruktor sat pri delu.

sat-from-proof : ∀ {φ} {ρ : Assignment} (p : eval-cnf ρ φ ≡ just true) → SatResult φ
sat-from-proof {ρ = ρ} p = sat ρ p


------------------------------------------------------------
-- Problem 11: NNF → CNF s Tseytinovo transformacijo
--
-- Za vsako notranje vozlišče uvedemo svežo spremenljivko xᵢ in dodamo
-- klavzule za xᵢ ↔ podformula (3 klavzule na ∧/∨ vozlišče). Rezultat je
-- equisatisfiabilen, ne ekvivalenten — tega formalno ne dokazujemo,
-- glej notes/11-tseytin.md.

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

-- tseytin vrne (naslednji prosti indeks, literal korena, zbrane klavzule)
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

to-cnf : NNF → CNF
to-cnf φ with tseytin φ (suc (max-var φ))
... | _ , root , cs = clauses-to-cnf (lit root) cs


------------------------------------------------------------
-- Problem 12: SAT za Formula
--
-- Cevovod: to-nnf → to-cnf → sat?. Ker Tseytin uvede sveže spremenljivke,
-- najdeni ρ na koncu še enkrat preverimo kar z eval na originalni formuli,
-- da dokaz živi na eval in ne na CNF.

data FormulaSat (φ : Formula) : Set where
  sat   : (ρ : Assignment) → eval ρ φ ≡ just true → FormulaSat φ
  unsat : FormulaSat φ

sat-formula? : (φ : Formula) → FormulaSat φ
sat-formula? φ with sat? (to-cnf (to-nnf φ))
... | unsat   = unsat
... | sat ρ _ with eval ρ φ in eq
...   | just true = sat ρ eq
...   | _         = unsat

sat-formula?-sound : ∀ {φ ρ p} → sat-formula? φ ≡ sat ρ p → eval ρ φ ≡ just true
sat-formula?-sound {p = p} _ = p

solve : Formula → Maybe Assignment
solve φ with sat-formula? φ
... | sat ρ _ = just ρ
... | unsat   = nothing
