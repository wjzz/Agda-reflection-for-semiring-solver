{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)

  2012-04-01

  A simple front-end to the Semiring solver specialized to ℕ, based on the Reflection API.
-}
module SolverFrontend where

-- usual modules

open import Data.Bool
open import Data.Empty
open import Data.Fin using (Fin;zero;suc;#_;fromℕ≤)
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Unit using (⊤;tt)
open import Data.Vec renaming (reverse to vreverse)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- semiring solver and reflection

open SemiringSolver
open import Data.Vec.N-ary
open import Reflection

--------------------------------------------
--  Extracting two sides of the equation  --
--------------------------------------------

≡' : Name
≡' = quote _≡_

-- returns true iff the term is the equality type,
-- ie. states the equality of two objects

isEquality : Term → Bool
isEquality (def f args) with f ≟-Name ≡'
isEquality (def f args) | yes p with args
isEquality (def f args) | yes p | x ∷ x₁ ∷ x₂ ∷ x₃ ∷ l = true

-- false otherwise
isEquality (def f args) | yes p | [] = false
isEquality (def f args) | yes p | x ∷ [] = false
isEquality (def f args) | yes p | x ∷ x₁ ∷ [] = false
isEquality (def f args) | yes p | x ∷ x₁ ∷ x₂ ∷ [] = false
isEquality (def f args) | no ¬p = false
isEquality (var x args) = false
isEquality (con c args) = false
isEquality (lam v t) = false
isEquality (pi t₁ t₂) = false
isEquality (sort x) = false
isEquality unknown = false

private 
  isEquality-ex : ∀ m n → true ≡ isEquality (quoteTerm (m + n ≡ n + m))
  isEquality-ex = λ m n → refl


-- returns (L , R) given L ≡ R and tt otherwise
-- takes a precondition so we don't have to polute our program with Maybes

extractEqParts : (t : Term) → .(eq : isEquality t ≡ true) → Term × Term
extractEqParts (def f args) eq with f ≟-Name ≡'
extractEqParts (def f args) eq | yes p with args
extractEqParts (def f args) eq | yes p | x ∷ x₀ ∷ arg v r lhs ∷ arg v₁ r₁ rhs ∷ l 
  = lhs , rhs

-- non-equality cases with false precondition
extractEqParts (def f args) () | yes p | [] 
extractEqParts (def f args) () | yes p | x ∷ [] 
extractEqParts (def f args) () | yes p | x ∷ x₁ ∷ [] 
extractEqParts (def f args) () | yes p | x ∷ x₁ ∷ x₂ ∷ [] 
extractEqParts (def f args) () | no ¬p 
extractEqParts (var x args) () 
extractEqParts (con c args) () 
extractEqParts (lam v t) ()
extractEqParts (pi t₁ t₂) ()
extractEqParts (sort x) ()
extractEqParts unknown ()

-- projections for particular sides of the equation

lhs : (t : Term) → .(eq : isEquality t ≡ true) → Term
lhs t eq = proj₁ (extractEqParts t eq)

rhs : (t : Term) → .(eq : isEquality t ≡ true) → Term
rhs t eq = proj₂ (extractEqParts t eq)

------------------------------------------------------------
--  Reflecting the structure of a term into a polynomial  --
------------------------------------------------------------

-- quoted names 

zero' : Name
zero' = quote Data.Nat.zero

suc' : Name
suc' = quote Data.Nat.suc

plus' : Name
plus' = quote Data.Nat._+_

mult' : Name
mult' = quote Data.Nat._*_

-- a function that checks if a given term is a polynomial on nats
-- n is the number of free variables in the term of type ℕ

isPoly : {n : ℕ} → Term → Bool
isPoly {n} (var x args) with suc x ≤? n
... | yes p = true
... | no ¬p = false

isPoly (con c args) with c ≟-Name zero'
isPoly (con c args) | yes _ = true
isPoly (con c args) | no _ with c ≟-Name suc'
isPoly (con c []) | no ¬p | yes p = false
isPoly {n} (con c (arg v r x ∷ args)) | no ¬p | yes p = isPoly {n} x
isPoly (con c args) | no ¬p₁ | no ¬p = false

isPoly (def f []) = false
isPoly (def f (x ∷ [])) = false
isPoly (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ args)) 
  with f ≟-Name plus'
isPoly {n} (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ args)) 
  | yes p = isPoly {n} x ∧ isPoly {n} x₁
isPoly (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ args))
  | no ¬p with f ≟-Name mult'
isPoly {n} (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ args)) 
  | no ¬p | yes p = isPoly {n} x ∧ isPoly {n} x₁
isPoly (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ args)) 
  | no ¬p₁ | no ¬p = false

isPoly (lam v t)  = false
isPoly (pi t₁ t₂) = false
isPoly (sort x)   = false
isPoly unknown    = false

-- isPoly examples

private

  isPoly-ex : isPoly {0} (quoteTerm 1) ≡ true
  isPoly-ex = refl

  isPoly-ex2 : (n m : ℕ) → isPoly {2} (quoteTerm (n + m)) ≡ true
  isPoly-ex2 n m = refl

  isPoly-ex3 : (n m : ℕ) → isPoly {2} (quoteTerm (n * m)) ≡ true
  isPoly-ex3 n m = refl

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

-- The main reflection helper.
-- Takes a term that is known to have the structure of a polynomial and
-- reflects its structure.

term2poly : {n : ℕ} (t : Term) 
          → .(isPoly {n} t ≡ true)
          → Polynomial n

term2poly {n} (var x args) eq with suc x ≤? n 
term2poly (var x args) eq | yes p = var (fromℕ≤ p)
term2poly (var x args) () | no ¬p

term2poly (con c args) eq with c ≟-Name zero'
term2poly (con c args) eq | yes p = con 0
term2poly (con c args) eq | no ¬p with c ≟-Name suc'
term2poly (con c []) () | no ¬p | yes p
term2poly (con c (arg v r x ∷ args)) eq | no ¬p | yes p = con 1 :+ term2poly x eq
term2poly (con c args) () | no ¬p₁ | no ¬p

term2poly (def f []) ()
term2poly (def f (x ∷ [])) ()
term2poly (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ args)) eq 
  with f ≟-Name plus'
term2poly (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ args)) eq 
  | yes p = term2poly x (and-l eq) :+ term2poly x₁ (and-r (isPoly x) (isPoly x₁) eq)
term2poly (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ args)) eq 
  | no ¬p with f ≟-Name mult'
term2poly (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ args)) eq 
  | no ¬p | yes p = term2poly x (and-l eq) :* term2poly x₁ (and-r (isPoly x) (isPoly x₁) eq)
term2poly (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ args)) () | no ¬p₁ | no ¬p

term2poly (lam v t) ()
term2poly (pi t₁ t₂) ()
term2poly (sort x) ()
term2poly unknown ()

-- examples

private

  term2poly-ex : term2poly {2} (quoteTerm 1) refl ≡ con 1 :+ con 0
  term2poly-ex = refl

  term2poly-ex2 : (m n : ℕ) → Polynomial 2
  term2poly-ex2 m n = term2poly (quoteTerm (m + m * n)) refl

  term2poly-ex3 : ∀ {m n} → term2poly-ex2 m n ≡ var (# 1) :+ (var (# 1) :* var (# 0))
  term2poly-ex3 = refl

--------------------------------------------------
--  Extracting the universally quantified nats  --
--------------------------------------------------

-- returns the number of the outermost pi quantified variables.

argsNo : Term → ℕ
argsNo (pi t₁ (el s t)) = suc (argsNo t)
argsNo (var x args) = 0
argsNo (con c args) = 0
argsNo (def f args) = 0
argsNo (lam v t) = 0
argsNo (sort x) = 0
argsNo unknown = 0

-- peels off all the outermost Pi constructors, 
-- returning a term with argsNo free variables.

stripPi : Term → Term
stripPi (pi t₁ (el s t)) = stripPi t

-- identity otherwise
stripPi (var x args) = var x args
stripPi (con c args) = con c args
stripPi (def f args) = def f args
stripPi (lam v t) = lam v t
stripPi (sort x)  = sort x
stripPi unknown   = unknown 

-- examples

private
  term-ex : Term
  term-ex = quoteTerm ((n m k : ℕ) → n + m ≡ m + k)

  argsNo-ex : argsNo term-ex ≡ 3
  argsNo-ex = refl

  -- simplefied notation, non-executable
  -- stripPi-ex : stripPi-ex t ≡ def ≡' (var 2 + var 1) ≡ (var 1 + var 0)

-------------------------------------------------------------------------
--  Wrapping the solve and prove function with the reflection helpers  --
-------------------------------------------------------------------------

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

------------------------------------------------------------------------------
-- A method that allows to drop 3 out of 4 refls, but cheats by using trustMe

open import Relation.Binary.PropositionalEquality.TrustMe

solv' : (t0 : Term) → 
       let n   = argsNo  t0 in
       let t   = stripPi t0 in
       let eq  = trustMe in
       let ipl = trustMe in
       let irl = trustMe in
       let l   = term2poly {n} (lhs t eq) ipl in
       let r   = term2poly {n} (rhs t eq) irl in
       let f   = build-eq-curry l r in
         Eqʰ n _≡_ (curryⁿ ⟦ proj₁ (close n f) ⟧↓) (curryⁿ ⟦ proj₂ (close n f) ⟧↓)
       → Eq  n _≡_ (curryⁿ ⟦ proj₁ (close n f) ⟧)  (curryⁿ ⟦ proj₂ (close n f) ⟧)

solv' t0 eqn =
  let n = argsNo  t0 in
  let t = stripPi t0 in
  let eq = trustMe in
  let ipl = trustMe in
  let irl = trustMe in
  let l = term2poly {n} (lhs t eq) ipl in
  let r = term2poly {n} (rhs t eq) irl in
  let f = build-eq-curry l r in
    solve n f eqn

{- Example usage 
lemma4 : ∀ m n → suc (m + n + (m + n)) ≡ m + m + suc (n + n)
lemma4 = quoteGoal e in solv' e refl
-}

