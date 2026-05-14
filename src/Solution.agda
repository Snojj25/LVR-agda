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
  using (ℕ; _≟_)
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
-- Problem 4.  Assoc  (a partial map  ℕ → Bool)
------------------------------------------------------------
--
-- We take the week-9 Assoc scaffolding and complete it,
-- specialising to  K = ℕ ,  V = Bool .  The carrier is a plain
-- association list; membership is defined by recursion as
--
--     k ∈ᴬ []                =  ⊥
--     k ∈ᴬ ((k′ , _) ∷ kvs)  =  (k ≡ k′)  ⊎  (k ∈ᴬ kvs)
--
-- — at the empty list there is no proof; at a cons either the head's
-- key matches or `k` is in the tail.  This recursive encoding has the
-- same content as an inductive  `here / there`  datatype but stays in
-- the standard  ⊥ / ⊎  vocabulary.
--
-- `insert` does in-place update: it walks the list, replacing an
-- existing binding for `k` if any, or appending otherwise.  Starting
-- from `empty = []` and only modifying through `insert`, the list
-- behaviourally has no duplicate keys, so `lookup` is deterministic.

infix 4 _∈ᴬ_

-- Membership of a key in an entry list.
_∈ᴬ_ : ℕ → List (ℕ × Bool) → Set
k ∈ᴬ []               = ⊥
k ∈ᴬ ((k′ , _) ∷ kvs) = (k ≡ k′) ⊎ (k ∈ᴬ kvs)
 
-- Value associated with a key, given a membership witness.
get : {k : ℕ} {kvs : List (ℕ × Bool)} → k ∈ᴬ kvs → Bool
get {kvs = []}              ()
get {kvs = (_ , v) ∷ _}     (inj₁ _) = v
get {kvs = (_ , _) ∷ kvs}   (inj₂ p) = get p

-- Decide membership — lifts  _≟_  on ℕ.
_∈ᴬ?_ : (k : ℕ) → (kvs : List (ℕ × Bool)) → Dec (k ∈ᴬ kvs)
k ∈ᴬ? []                = no λ ()
k ∈ᴬ? ((k′ , _) ∷ kvs)  with k ≟ k′
... | yes refl = yes (inj₁ refl)  -- head matches
... | no  k≢k′ with k ∈ᴬ? kvs  
...   | yes p     = yes (inj₂ p)  -- tail matches
...   | no  k∉kvs = no λ { (inj₁ p) → k≢k′ p
                         ; (inj₂ p) → k∉kvs p }

-- The carrier.
Assignment : Set
Assignment = List (ℕ × Bool)

-- The empty assignment.
empty : Assignment
empty = []

-- Maybe-typed lookup, the function used by the evaluators.
lookup : ℕ → Assignment → Maybe Bool
lookup k ρ with k ∈ᴬ? ρ
... | yes p = just (get p)
... | no  _ = nothing

-- Insert: replace existing binding for `k`, or append if not present.
insert : ℕ → Bool → Assignment → Assignment
insert k v []                = (k , v) ∷ []
insert k v ((k′ , v′) ∷ ρ)   with k ≟ k′
... | yes _ = (k , v) ∷ ρ
... | no  _ = (k′ , v′) ∷ insert k v ρ


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

-- Splitting-rule search.
--
--   sat-search vs ρ φ  =  true   iff some extension of ρ that
--                                  assigns every v ∈ vs makes φ true.
--
-- Termination is by structural recursion on the list  vs .  Duplicate
-- entries in  vs  cause re-branching on the same variable, which is
-- wasteful but harmless: `insert` replaces the previous binding.

sat-search : List ℕ → Assignment → CNF → Bool
sat-search [] ρ φ with eval-cnf ρ φ
... | just true  = true
... | _          = false
sat-search (v ∷ vs) ρ φ =
      sat-search vs (insert v true  ρ) φ
   or sat-search vs (insert v false ρ) φ

sat? : CNF → Bool
sat? φ = sat-search (cnf-vars φ) empty φ


------------------------------------------------------------
-- Problem 10.  NNF → CNF  (naive distribution)
------------------------------------------------------------
--
-- We push ∨ underneath ∧ using the distributive law
--
--     a ∨ (b ∧ c)  ≡  (a ∨ b) ∧ (a ∨ c) .
--
-- This is *equivalence-preserving* (in particular,
-- equisatisfiability-preserving, which is what the project asks for).
-- The trade-off is that the output can be exponentially larger than
-- the input — a sharper Tseytin-style transformation would avoid the
-- blow-up at the cost of introducing fresh variables and only
-- preserving equisatisfiability.  For the project's grammar and
-- sized inputs this simpler version is fine.

-- Disjunct ∨ Disjunct: append two clauses' literal lists.
_∨d++_ : Disjunct → Disjunct → Disjunct
lit ℓ    ∨d++ d = ℓ ∨d d
(ℓ ∨d e) ∨d++ d = ℓ ∨d (e ∨d++ d)

infixr 6 _∨d++_

-- CNF ∧ CNF: append two clause lists.
_∧c++_ : CNF → CNF → CNF
dis d    ∧c++ c′ = d ∧c c′
(d ∧c c) ∧c++ c′ = d ∧c (c ∧c++ c′)

infixr 7 _∧c++_

-- Distribute a single clause across a CNF:
--   D ∨ (c₁ ∧ … ∧ cₙ)  ≡  (D ∨ c₁) ∧ … ∧ (D ∨ cₙ)
distrib-l : Disjunct → CNF → CNF
distrib-l D (dis e)   = dis (D ∨d++ e)
distrib-l D (e ∧c c)  = (D ∨d++ e) ∧c distrib-l D c

-- Distribute two CNFs:
--   (c₁ ∧ … ∧ cₙ) ∨ (c′₁ ∧ … ∧ c′ₘ)
distrib : CNF → CNF → CNF
distrib (dis D)  c′ = distrib-l D c′
distrib (D ∧c c) c′ = distrib-l D c′ ∧c++ distrib c c′

-- Top-level conversion.
to-cnf : NNF → CNF
to-cnf (lit ℓ)   = dis (lit ℓ)
to-cnf (a ∧n b)  = to-cnf a ∧c++ to-cnf b
to-cnf (a ∨n b)  = distrib (to-cnf a) (to-cnf b)
