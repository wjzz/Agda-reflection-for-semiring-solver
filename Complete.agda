{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)

  2012-04-02

  A simple front-end to the Semiring solver specialized to ℕ, based on the Reflection API.

  A top-level description of the reflection algorithm:
    1. calculate the number of top-level quantifiers of the goal
    2. strip all of those quantifiers (until we find the refl' type)
    3. extract both sides of the A ≡ B equation
    4. ...
    TODO
-}
module Complete where

-- usual modules

open import Category.Monad.State
open import Data.Bool
open import Data.Empty
open import Data.Fin using (Fin;zero;suc;#_;fromℕ≤;raise;inject≤)
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit using (⊤;tt)
open import Data.Vec using (Vec; []; _∷_; fromList) renaming (reverse to vreverse)
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- semiring solver and reflection

open import Data.Vec.N-ary
open import Reflection renaming (_≟_ to _≟-Term_)
import Algebra.RingSolver as AR
open SemiringSolver

-- Boolean helpers
-- Agda is able to infer b and b' in and-l but not in and-r, hence the contrast.

private

  and-l : ∀ {b b'} → b ∧ b' ≡ true → b ≡ true
  and-l {true}  eq = refl
  and-l {false} eq = eq

  and-r : ∀ b b' → b ∧ b' ≡ true → b' ≡ true
  and-r true  b'    eq = eq
  and-r false true  eq = refl
  and-r false false eq = eq

--------------------------------------------------
--  Extracting the universally quantified nats  --
--------------------------------------------------

-- returns the number of the outermost pi quantified variables.

argsNo : Term → ℕ
argsNo (pi t₁ (el s t)) = suc (argsNo t)
argsNo (var x args) = 0
argsNo (con c args) = 0
argsNo (def f args) = 0
argsNo (lam v t)    = 0
argsNo (sort x)     = 0
argsNo unknown      = 0

-- peels off all the outermost Pi constructors, 
-- returning a term with argsNo more free variables compared to the input term.

stripPi : Term → Term
stripPi (pi t₁ (el s t)) = stripPi t

-- identity otherwise

stripPi (var x args) = var x args
stripPi (con c args) = con c args
stripPi (def f args) = def f args
stripPi (lam v t)    = lam v t
stripPi (sort x)     = sort x
stripPi unknown      = unknown 

-- examples

private
  term-ex : Term
  term-ex = quoteTerm ((n m k : ℕ) → n + m ≡ m + k)

  argsNo-ex : argsNo term-ex ≡ 3
  argsNo-ex = refl

  -- simplefied notation, non-executable
  -- stripPi-ex : stripPi-ex t ≡ def ≡' (var 2 + var 1) ≡ (var 1 + var 0)

--------------------------------------------
--  Extracting two sides of the equation  --
--------------------------------------------

≡' : Name
≡' = quote _≡_

extractEq : Term → Term × Term
extractEq (def f args) with f ≟-Name ≡' 
extractEq (def f args) | yes p with args
extractEq (def f args) | yes p | _ ∷ _ ∷ arg v r lhs ∷ arg v₁ r₁ rhs ∷ l = lhs , rhs
extractEq (def f args) | yes p | _  = unknown , unknown
extractEq (def f args) | no  _ = unknown , unknown
extractEq _ = unknown , unknown

lhs' : Term → Term
lhs' = proj₁ ∘ extractEq

rhs' : Term → Term
rhs' = proj₂ ∘ extractEq

------------------------------------------------------------
--  Reflecting the structure of a term into a polynomial  --
------------------------------------------------------------

-- quoted names 

zero' = quote Data.Nat.zero
suc'  = quote Data.Nat.suc
plus' = quote Data.Nat._+_
mult' = quote Data.Nat._*_

---------------------------
--  A modified approach  --
---------------------------

{- Vocabulary:

  consider an example goal:

  (G)    ∀ m n → suc m + pred n + n ≡ pred n + m + m + 1

  The semiring solver has no knowledge of the pred symbol, so to solve G we
  should abstract over all occurences of 'pred n', effectively solving a goal G':

  (G)    ∀ m n k → suc m + k + n + n ≡ k + m + m + 1

  Terms build only with suc, +, * and variables universally quantified in the goal
  are easy to deal with. The simple solver actually deals with exclusively with
  this kind of expressions. We will call such terms ??? 

  Terms that we cannot decompose in this framework (such as pred n, foo n m etc)
  will be called atoms.
-}


-- State monad preparations

Atoms     = List Term
AtomState = State Atoms

open RawMonadState (StateMonadState Atoms)

-- Dominuque Devriese's notation with do and then replaced by ⟨ and ⟩ resp.
-- a trick needed because we can't use a mixfix inside a bind
bind : ∀ {A B} → AtomState A → (A → AtomState B) → AtomState B
bind = _>>=_

syntax bind m (\ x → c) = ⟨ x ← m ⟩ c


-- Extends the list of known atoms if given a new one;
-- otherwise returns the original list

member : Term → Atoms → Bool
member t [] = false
member t (x ∷ xs) with t ≟-Term x
... | yes _ = true
... | no  _ = member t xs

tryAdd : Term → Atoms → Atoms
tryAdd t l with member t l
... | true  = l
... | false = t ∷ l

tryAddM : Term → AtomState ⊤
tryAddM t = modify (tryAdd t)
         >> return tt
  
-- Returns a list of all atoms found in the term (no duplicates).
-- 
-- The state contains a list with atoms already found somewhere else,
--   this way we know when we found a previously unseen one.
-- The index tells us the number of known free vars. 
--   It will be set to argsNo of the initial term.


isBinaryOp : Name → Bool
isBinaryOp n with n ≟-Name plus' | n ≟-Name mult'
... | no _ | no _ = false
... | _    | _    = true

distinctAtomsM : {n : ℕ} → Term → AtomState ⊤
distinctAtomsM {n} (var x args) with suc x ≤? n
distinctAtomsM (var x args) | yes p = return tt
distinctAtomsM (var x args) | no ¬p = tryAddM (var x args)

distinctAtomsM (con c args) with c ≟-Name zero'
distinctAtomsM (con c args) | yes p = return tt
distinctAtomsM (con c args) | no ¬p with c ≟-Name suc'
distinctAtomsM (con c [])              | no ¬p | yes p = return tt
distinctAtomsM (con c (x ∷ x₁ ∷ args)) | no ¬p | yes p = return tt
distinctAtomsM {n} (con c (arg v r x ∷ [])) | no ¬p | yes p = distinctAtomsM {n} x
-- neither zero nor suc, so atomic
distinctAtomsM (con c args) | no ¬p₁ | no ¬p = tryAddM (con c args)

distinctAtomsM (def f (x ∷ x₁ ∷ [])) with isBinaryOp f
... | false = tryAddM (def f (x ∷ x₁ ∷ []))
distinctAtomsM {n} (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | true 
  = distinctAtomsM {n} x 
 >> distinctAtomsM {n} x₁

distinctAtomsM (def f args) = tryAddM (def f args)
-- distinctAtomsM (def f []) = {!!}
-- distinctAtomsM (def f (x ∷ [])) = {!!}
-- distinctAtomsM (def f (x ∷ x₁ ∷ x₂ ∷ args)) = {!!}

distinctAtomsM (lam v t)  = return tt
distinctAtomsM (pi t₁ t₂) = return tt
distinctAtomsM (sort x)   = return tt
distinctAtomsM unknown    = return tt

distinctAtoms : {n : ℕ} → Term → Atoms → Atoms
distinctAtoms {n} t atoms = proj₂ (distinctAtomsM {n} t atoms) 

-- the function we fought for in this section

-- Returns all atoms from both sides of the equation
-- TODO: if the goal is solvable, then distinctAtoms l [] should have the same elements as
-- distinctAtoms r []. in the current version the second traversal is a waste of computation power...

distinctAtomsEq : {n : ℕ} → Term → Term → Atoms
distinctAtomsEq {n} l r = distinctAtoms {n} l (distinctAtoms {n} r [])

-------------------------------------------
--  Extracting the polynomial structure  --
-------------------------------------------

-- Returns the index of the element in the vector if the element is found,
-- nothing otherwise.
-- 
-- tryFind t v == just i   ==>  lookup v i == t

tryFind : ∀ {m} → Term → Vec Term m → Maybe (Fin m)
tryFind t [] = nothing
tryFind t (x ∷ xs) with t ≟-Term x
... | yes p = just zero
... | no ¬p with tryFind t xs
... | nothing = nothing
... | just i  = just (suc i)

-- A placeholder polynomial, it's a small hack.

dummy : ∀ {n} → Polynomial n
dummy = con 0

-- Finds the given atom in the atoms list and returns a variable
-- with the index raised by n.

findAtom : ∀ {n m}
         → (atoms : Vec Term m)
         → (t : Term)
         → Polynomial (n + m)
findAtom atoms t with tryFind t atoms
findAtom {n} atoms t | just i  = var (raise n i)
findAtom     atoms t | nothing = dummy

-- Returns a combining function if given the name of a binary operator,
-- nothing otherwise.

tryBinaryOp : ∀ {k} Name → Maybe (Polynomial k → Polynomial k → Polynomial k)
tryBinaryOp n with n ≟-Name plus' | n ≟-Name mult'
tryBinaryOp n | yes p | r2     = just _:+_
tryBinaryOp n | no ¬p | yes p  = just _:*_
tryBinaryOp n | no ¬p | no ¬p₁ = nothing

-- Builds a polynomial from a term.
--
-- The result polynomial has n+m free variables.
-- The first n indexes are for variables universally quantified in the goal,
-- the next m indexes are for the atomic terms collected in the atoms vector.

term2poly : {n : ℕ}
            {m : ℕ}
          → (atoms : Vec Term m)
          → (t : Term)
          → Polynomial (n + m)

term2poly {n} {m} atoms t = t2p t where

  t2p : Term → Polynomial (n + m)

  t2p (var x args) with suc x ≤? n
  ... | yes p = var (inject≤ (fromℕ≤ p) (m≤m+n n m))
  ... | no ¬p = findAtom {n} atoms (var x args)

  t2p (con c args)             with c ≟-Name zero'
  t2p (con c args)             | yes _ = con 0
  t2p (con c args)             | no  _ with c ≟-Name suc'
  t2p (con c (arg r v x ∷ [])) | no _ | yes _ = con 1 :+ t2p x
  t2p (con c not-singleton)    | no _ | yes _ = dummy
  t2p (con c args)             | no _ | no  _ = findAtom {n} atoms (con c args)

  t2p (def f args)                            with tryBinaryOp {n + m} f
  t2p (def f (arg r v x ∷ arg r' v' x₁ ∷ [])) | just o  = o (t2p x) (t2p x₁)  
  t2p (def f not-exactly-two-args)            | just o  = dummy
  t2p (def f args)                            | nothing = findAtom {n} atoms (def f args)

  t2p (lam v t₁) = dummy
  t2p (pi t₁ t₂) = dummy
  t2p (sort x)   = dummy
  t2p unknown    = dummy

--------------------
--  Test tactics  --
--------------------

debugGoal : (g : Term)
          → let t = stripPi g in
            ∃ (λ k → Polynomial k × Polynomial k)
debugGoal g =
  let t      = stripPi g in
  let n      = argsNo  g in
  let atomsL = distinctAtomsEq {n} (lhs' t) (rhs' t) in
  let m      = length atomsL in
  let atoms  = fromList atomsL in
  (n + m , (term2poly {n} atoms (lhs' t) , term2poly {n} atoms (rhs' t)))

-------------------------------------------------------------------------
--  Wrapping the solve and prove function with the reflection helpers  --
-------------------------------------------------------------------------
{-
-- first version

kill : {n   : ℕ} 
     → (t   : Term) 
     → (ρ   : Vec ℕ n)
     → (eq  : isEquality t ≡ true)
     → (ipl : isPoly {n} (lhs t eq) ≡ true)
     → (irl : isPoly {n} (rhs t eq) ≡ true)
     → ⟦ term2poly (lhs t eq) ipl ⟧↓ ρ ≡ ⟦ term2poly (rhs t eq) irl ⟧↓ ρ 
     → ⟦ term2poly (lhs t eq) ipl ⟧  ρ ≡ ⟦ term2poly (rhs t eq) irl ⟧  ρ

kill t ρ eq ipl irl eq2 = prove ρ (term2poly (lhs t eq) ipl) (term2poly (rhs t eq) irl) eq2

{- Example usage
lemma : ∀ m n → suc (m + n + (m + n)) ≡ m + m + suc (n + n)
lemma m n = quoteGoal e in kill e (n ∷ m ∷ []) refl refl refl refl
-}

kil2 : (t0   : Term) → 
     let n = argsNo  t0 in
     let t = stripPi t0 in
     (ρ   : Vec ℕ n)
     → (eq  : isEquality t ≡ true)
     → (ipl : isPoly {n} (lhs t eq) ≡ true)
     → (irl : isPoly {n} (rhs t eq) ≡ true)
     → ⟦ term2poly (lhs t eq) ipl ⟧↓ ρ ≡ ⟦ term2poly (rhs t eq) irl ⟧↓ ρ 
     → ⟦ term2poly (lhs t eq) ipl ⟧  ρ ≡ ⟦ term2poly (rhs t eq) irl ⟧  ρ

kil2 t0 ρ eq ipl irl eq2 = 
  let t = stripPi t0 
  in  prove ρ (term2poly (lhs t eq) ipl) (term2poly (rhs t eq) irl) eq2

{- Example usage
lemma' : ∀ m n → suc (m + n + (m + n)) ≡ m + m + suc (n + n)
lemma' = quoteGoal e in λ m n → kil2 e (n ∷ m ∷ []) refl refl refl refl
-}

-------------------------------------------
-- The version with maximal reflection


-- Bind from the substituion monad
-- 
-- We essentially use this function to close the n free 
-- variables we got from the Reflection API by using stripPi.

psubst : {n : ℕ} → Polynomial n → Vec (Polynomial n) n → Polynomial n
psubst (op o e e₁) ρ = op o (psubst e ρ) (psubst e₁ ρ)
psubst (con c)     ρ = con c
psubst (var x)     ρ = lookup x ρ
psubst (_:^_ e n₁) ρ = psubst e ρ :^ n₁ 
psubst (:-_ e)     ρ = :- psubst e ρ

-- element-wise subst in a pair

build-eq : {n : ℕ} 
         → (lhs rhs : Polynomial n) 
         → Vec (Polynomial n) n 
         → (Polynomial n × Polynomial n)

build-eq e₁ e₂ ρ = psubst e₁ (vreverse ρ) , psubst e₂ (vreverse ρ)

-- function copied from stdlib's Relation.Binary.Reflection
-- 
-- One can get this function by saying
--   open Reflection setoid var ⟦_⟧ ⟦_⟧↓ (nf-sound ∘ normalise)
--     public using (close; prove; solve) renaming (_⊜_ to _:=_)
-- insteated of
--   open Reflection setoid var ⟦_⟧ ⟦_⟧↓ (nf-sound ∘ normalise)
--     public using (prove; solve) renaming (_⊜_ to _:=_)
-- in the Algebra.RingSolver stdlib's module

-- Applies the function to all possible "variables".

close : ∀ {A : Set} n → N-ary n (Polynomial n) A → A
close n f = f $ⁿ Data.Vec.map var (allFin n)

-- curried version of build-eq

build-eq-curry : {n : ℕ} → (lhs rhs : Polynomial n) 
               → N-ary n (Polynomial n) (Polynomial n × Polynomial n)

build-eq-curry lhs rhs = curryⁿ (build-eq lhs rhs)

-- calculating front-end for solve

ring : (t0 : Term) → 
       let n = argsNo  t0 in
       let t = stripPi t0 in
       (eq  : isEquality t ≡ true)
     → (ipl : isPoly {n} (lhs t eq) ≡ true)
     → (irl : isPoly {n} (rhs t eq) ≡ true) → 
       let l = term2poly (lhs t eq) ipl in
       let r = term2poly (rhs t eq) irl in
       let f = build-eq-curry l r in
       Eqʰ n _≡_ (curryⁿ ⟦ proj₁ (close n f) ⟧↓) (curryⁿ ⟦ proj₂ (close n f) ⟧↓)
     → Eq  n _≡_ (curryⁿ ⟦ proj₁ (close n f) ⟧)  (curryⁿ ⟦ proj₂ (close n f) ⟧)

ring t0 eq ipl irl eqn =
  let n = argsNo  t0 in
  let t = stripPi t0 in
  let l = term2poly (lhs t eq) ipl in
  let r = term2poly (rhs t eq) irl in
  let f = build-eq-curry l r in
   solve n f eqn
  
{- Example usage
lemma3 : ∀ m n → suc (m + n + (m + n)) ≡ m + m + suc (n + n)
lemma3 = quoteGoal e in ring e refl refl refl refl
-}

-}

------------------
--  Unit tests  --
------------------

unit-test-0 : ∀ n m → n + m + 1 ≡ suc (m + n)
unit-test-0 = {!!}

unit-test-1 : ℕ → ℕ
unit-test-1 n = n where
  lemma : ∀ m → m + n ≡ n + m
  lemma = quoteGoal g in {!debugGoalVal g!}

unit-test-2 : ∀ n m → pred n + pred m ≡ pred m + pred n
unit-test-2 = {!!}

------------------
--  Playground  --
------------------

unit-test-3 : ∀ n m → n + m + pred n + pred m ≡ pred m + pred n + n + m
unit-test-3 = quoteGoal g in {!debugGoal g!}

unit-test-4 : ∀ n m → n + m + pred n + pred m ≡ pred m + pred n + n + m
unit-test-4 = quoteGoal g in {!extractEq (stripPi g)!}
