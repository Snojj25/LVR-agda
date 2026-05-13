------------------------------------------------------------
-- Logika v Računalništvu — Project Solution
--
-- Solves Problems 1–10 of the project.
-- All ten problems are answered in this single file, in order.
-- Companion explanations live under  notes/ .
------------------------------------------------------------

module Solution where

------------------------------------------------------------
-- Imports from the Agda standard library
------------------------------------------------------------

open import Data.Nat
  using (ℕ; suc; _≟_; _⊔_)
open import Data.Bool
  using (Bool; true; false; not)
  renaming (_∧_ to _and_; _∨_ to _or_)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.List
  using (List; []; _∷_; _++_)
open import Data.Product
  using (_×_; _,_)
open import Relation.Nullary
  using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)


------------------------------------------------------------
-- Problem 1.  Formula
------------------------------------------------------------
--
-- Inductive type implementing the grammar
--    Formula → Var n | ¬ Formula | Formula ∧ Formula | Formula ∨ Formula
--
-- We use the constructors  var , ¬f_ , _∧f_ , _∨f_  to avoid
-- clashing with the homonymous operators on Bool.

data Formula : Set where
  var  : ℕ → Formula
  ¬f_  : Formula → Formula
  _∧f_ : Formula → Formula → Formula
  _∨f_ : Formula → Formula → Formula

infix  9 ¬f_
infixr 7 _∧f_
infixr 6 _∨f_


------------------------------------------------------------
-- Problem 2.  NNF (Negation Normal Form)
------------------------------------------------------------
--
-- A literal is either a variable (positive) or a negated variable
-- (negative); negation appears nowhere else in an NNF formula.

data Literal : Set where
  pos : ℕ → Literal     -- the literal  Var n
  neg : ℕ → Literal     -- the literal  ¬ Var n

data NNF : Set where
  lit  : Literal → NNF
  _∧n_ : NNF → NNF → NNF
  _∨n_ : NNF → NNF → NNF

infixr 7 _∧n_
infixr 6 _∨n_


------------------------------------------------------------
-- Problem 3.  Conversion  Formula → NNF
------------------------------------------------------------
--
-- We push every ¬ down to the variables using De Morgan's laws
-- and ¬¬φ ≡ φ.  To make the recursion structurally obvious (and so
-- it is accepted by Agda's termination checker) we define two
-- mutually-recursive helpers:
--
--    nnf⁺ φ   produces an NNF equivalent to     φ
--    nnf⁻ φ   produces an NNF equivalent to    ¬ φ
--
-- Both recurse only on strictly smaller sub-formulas.

nnf⁺ : Formula → NNF
nnf⁻ : Formula → NNF

nnf⁺ (var n)   = lit (pos n)
nnf⁺ (¬f φ)    = nnf⁻ φ
nnf⁺ (a ∧f b)  = nnf⁺ a ∧n nnf⁺ b
nnf⁺ (a ∨f b)  = nnf⁺ a ∨n nnf⁺ b

nnf⁻ (var n)   = lit (neg n)
nnf⁻ (¬f φ)    = nnf⁺ φ                 -- ¬¬φ ≡ φ
nnf⁻ (a ∧f b)  = nnf⁻ a ∨n nnf⁻ b       -- ¬(a∧b) ≡ ¬a ∨ ¬b
nnf⁻ (a ∨f b)  = nnf⁻ a ∧n nnf⁻ b       -- ¬(a∨b) ≡ ¬a ∧ ¬b

to-nnf : Formula → NNF
to-nnf = nnf⁺


------------------------------------------------------------
-- Problem 4.  Assoc  (week-9 `AssocList` module, completed)
------------------------------------------------------------
--
-- We follow `Ex9.agda` literally: a `DecType` record packages
-- a carrier `Set` with a decidable equality, and `AssocList`
-- is parametric in `(K : DecType) (V : Set)`.  Every hole from
-- Ex9 is filled below.
--
-- To recover the project's `open Assoc ℕ test-≡ Bool` shape we
-- instantiate with `K = 𝒩` and `V = Bool` and re-export the
-- module's `Assoc` type as `Assignment`.

record DecType : Set₁ where
  field
    carr   : Set
    test-≡ : (x y : carr) → Dec (x ≡ y)
open DecType

---------------
-- copied from Ex9.agda (Exercise 7): AssocList interface
---------------
module AssocList (K : DecType) (V : Set) where

  Assoc : Set
  Assoc = List (carr K × V)

  {- Elementhood relation -}
  infix 4 _∈_
  -- ------my code----
  data _∈_ : carr K → Assoc → Set where
    here  : ∀ {k v kvs}     → k ∈ ((k  , v ) ∷ kvs)
    there : ∀ {k k′ v′ kvs} → k ∈ kvs → k ∈ ((k′ , v′) ∷ kvs)
  -- ------my code----

  {- Safe lookup -}
  lookup : {k : carr K} {kvs : Assoc} → k ∈ kvs → V
  -- ------my code----
  lookup {kvs = (_ , v) ∷ _}   here      = v
  lookup {kvs = (_ , _) ∷ kvs} (there p) = lookup {kvs = kvs} p
  -- ------my code----

  {- The decidability of the elementhood relation -}
  infix 4 _∈?_
  _∈?_ : (k : carr K) → (kvs : Assoc) → Dec (k ∈ kvs)
  -- ------my code----
  k ∈? [] = no (λ ())
  k ∈? ((k′ , _) ∷ kvs) with test-≡ K k k′
  ... | yes refl = yes here
  ... | no  k≢k′ with k ∈? kvs
  ...   | yes p  = yes (there p)
  ...   | no  ¬p = no λ where
            here      → k≢k′ refl
            (there q) → ¬p q
  -- ------my code----

  {- Lookup returning a maybe -}
  infixl 9 _‼_
  _‼_ : (kvs : Assoc) → (k : carr K) → Maybe V
  -- ------my code----
  kvs ‼ k with k ∈? kvs
  ... | yes p = just (lookup p)
  ... | no  _ = nothing
  -- ------my code----

  {-
     Update value

     Note: Here if `k` is not in `kvs` we append it to the front, otherwise we
     step into `kvs` and replace the odl value with the new value.
  -}
  infixl 8 _[_]≔_
  _[_]≔_ : Assoc → carr K → V → Assoc
  -- ------my code----
  []                [ k ]≔ v = (k , v) ∷ []
  ((k′ , v′) ∷ kvs) [ k ]≔ v with test-≡ K k k′
  ... | yes _ = (k  , v ) ∷ kvs
  ... | no  _ = (k′ , v′) ∷ (kvs [ k ]≔ v)
  -- ------my code----

------------------------------------------------------------
-- ℕ as a `DecType`, and the project-style instantiation.
------------------------------------------------------------

---------------
-- additional project glue (instantiation for Problem 4)
---------------
𝒩 : DecType
carr   𝒩 = ℕ
test-≡ 𝒩 = _≟_

open AssocList 𝒩 Bool public hiding (lookup)

Assignment : Set
Assignment = Assoc

-- Convenience wrappers used by Problems 5–10.
empty : Assignment
empty = []

insert : ℕ → Bool → Assignment → Assignment
insert k v ρ = ρ [ k ]≔ v

lookup : ℕ → Assignment → Maybe Bool
lookup k ρ = ρ ‼ k


------------------------------------------------------------
-- Problem 5.  Evaluating a Formula
------------------------------------------------------------
--
--   eval ρ φ  =  just (truth value of φ under ρ)   if every
--                                                  variable in φ
--                                                  is bound by ρ;
--             =  nothing                           otherwise.

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


------------------------------------------------------------
-- Problem 6.  Evaluating an NNF
------------------------------------------------------------

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
-- Problem 7.  CNF (Conjunctive Normal Form)
------------------------------------------------------------
--
-- A Disjunct is a non-empty disjunction of literals,
-- a CNF      is a non-empty conjunction of disjuncts.
--
-- Note: the project's grammar prints  CNF → Disjunct ∨ CNF ,
--   which is almost certainly a typo: a *conjunctive* normal form
--   is a *conjunction* of disjuncts, hence ∧ , not ∨ .  We also add
--   the obvious base case  CNF → Disjunct  so that the grammar
--   actually generates non-empty CNFs.

data Disjunct : Set where
  lit  : Literal → Disjunct
  _∨d_ : Literal → Disjunct → Disjunct

data CNF : Set where
  dis  : Disjunct → CNF
  _∧c_ : Disjunct → CNF → CNF

infixr 6 _∨d_
infixr 7 _∧c_


------------------------------------------------------------
-- Problem 8.  Evaluating a CNF
------------------------------------------------------------

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
-- Problem 9.  SAT solver for CNF
------------------------------------------------------------
--
-- We implement a DPLL-flavoured solver based on the *splitting
-- rule*:  to decide whether φ is satisfiable, split on a variable v
-- and recurse on  φ[v↦true]  and  φ[v↦false] .  Both subproblems
-- have one less free variable, so termination is structural on the
-- list of unassigned variables.
--
-- Refinements like unit propagation and pure-literal elimination
-- can be layered on top; we discuss them in the notes.  The core
-- solver below is sound and complete for finite CNFs.

-- The variable index of a literal.
lit-var : Literal → ℕ
lit-var (pos n) = n
lit-var (neg n) = n

-- Variable indices appearing in a Disjunct / CNF (with duplicates).
dis-vars : Disjunct → List ℕ
dis-vars (lit ℓ)   = lit-var ℓ ∷ []
dis-vars (ℓ ∨d d)  = lit-var ℓ ∷ dis-vars d

cnf-vars : CNF → List ℕ
cnf-vars (dis d)   = dis-vars d
cnf-vars (d ∧c φ)  = dis-vars d ++ cnf-vars φ

-- Membership test on a list of ℕ, used to deduplicate.
mem? : ℕ → List ℕ → Bool
mem? _ []        = false
mem? n (m ∷ ms)  with n ≟ m
... | yes _ = true
... | no  _ = mem? n ms

dedup : List ℕ → List ℕ
dedup []        = []
dedup (n ∷ ns)  with mem? n (dedup ns)
... | true  = dedup ns
... | false = n ∷ dedup ns

-- Brute-force / splitting-rule search.
--
--   sat-search vs ρ φ  =  true   iff some extension of ρ that
--                                  assigns every v ∈ vs makes φ true.
--
-- Termination is by structural recursion on the list  vs .

sat-search : List ℕ → Assignment → CNF → Bool
sat-search [] ρ φ with eval-cnf ρ φ
... | just true  = true
... | _          = false
sat-search (v ∷ vs) ρ φ =
      sat-search vs (insert v true  ρ) φ
   or sat-search vs (insert v false ρ) φ

sat? : CNF → Bool
sat? φ = sat-search (dedup (cnf-vars φ)) empty φ


------------------------------------------------------------
-- Problem 10.  Tseytin transformation  NNF → CNF
------------------------------------------------------------
--
-- We give the standard Tseytin transformation: for every internal
-- node of the NNF we introduce a fresh variable  x  representing
-- "the value of this subformula" and add 2 or 3 clauses encoding
--
--      x  ↔  l_a  ∧/∨  l_b   .
--
-- The result is *equisatisfiable* (not equivalent) to the input
-- but its size is linear in |φ|, whereas naive distribution can
-- explode exponentially.
--
-- Convention used below: tseytin-aux returns a triple
--    (next , top , clauses)
-- where  next  is the next unused variable index,  top  is the
-- literal representing the value of the whole subformula, and
-- clauses are the CNF constraints accumulated so far.

-- Negation of a literal.
flip : Literal → Literal
flip (pos n) = neg n
flip (neg n) = pos n

-- Largest variable index in an NNF (so  suc max-var  is always fresh).
max-var : NNF → ℕ
max-var (lit (pos n)) = n
max-var (lit (neg n)) = n
max-var (a ∧n b)      = max-var a ⊔ max-var b
max-var (a ∨n b)      = max-var a ⊔ max-var b

-- Build a Disjunct out of a head literal and a list of tail literals.
disjunct-of : Literal → List Literal → Disjunct
disjunct-of ℓ []        = lit ℓ
disjunct-of ℓ (m ∷ ms)  = ℓ ∨d disjunct-of m ms

-- Glue a list of disjuncts into a CNF (with at least one disjunct).
cnf-of : Disjunct → List Disjunct → CNF
cnf-of d []        = dis d
cnf-of d (e ∷ es)  = d ∧c cnf-of e es

-- The core recursion.
tseytin-aux : ℕ → NNF → ℕ × Literal × List Disjunct
tseytin-aux n (lit ℓ) = n , ℓ , []
tseytin-aux n (a ∧n b) with tseytin-aux n a
... | n₁ , la , cs₁ with tseytin-aux n₁ b
...   | n₂ , lb , cs₂ =
            let x   = n₂
                n₃  = suc n₂
                -- x ↔ (la ∧ lb) :
                --   ¬x ∨ la            (x ⇒ la)
                --   ¬x ∨ lb            (x ⇒ lb)
                --   ¬la ∨ ¬lb ∨ x      (la ∧ lb ⇒ x)
                c₁ = disjunct-of (neg x) (la ∷ [])
                c₂ = disjunct-of (neg x) (lb ∷ [])
                c₃ = disjunct-of (flip la) (flip lb ∷ pos x ∷ [])
            in n₃ , pos x , c₁ ∷ c₂ ∷ c₃ ∷ cs₁ ++ cs₂
tseytin-aux n (a ∨n b) with tseytin-aux n a
... | n₁ , la , cs₁ with tseytin-aux n₁ b
...   | n₂ , lb , cs₂ =
            let x   = n₂
                n₃  = suc n₂
                -- x ↔ (la ∨ lb) :
                --   ¬x ∨ la ∨ lb       (x ⇒ la ∨ lb)
                --   ¬la ∨ x            (la ⇒ x)
                --   ¬lb ∨ x            (lb ⇒ x)
                c₁ = disjunct-of (neg x) (la ∷ lb ∷ [])
                c₂ = disjunct-of (flip la) (pos x ∷ [])
                c₃ = disjunct-of (flip lb) (pos x ∷ [])
            in n₃ , pos x , c₁ ∷ c₂ ∷ c₃ ∷ cs₁ ++ cs₂

-- Top-level Tseytin: produce a CNF asserting that the top
-- representative literal is true.
tseytin : NNF → CNF
tseytin φ with tseytin-aux (suc (max-var φ)) φ
... | _ , top , cs = cnf-of (lit top) cs
