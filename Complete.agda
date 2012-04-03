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

zero' = quote Data.Nat.zero
suc'  = quote Data.Nat.suc
plus' = quote Data.Nat._+_
mult' = quote Data.Nat._*_

{-
------------------------------------------------
--  A test approach: well-formed expressions  --
------------------------------------------------

data validTerm (n : ℕ) : Term → Set where

  var1 : ∀ {x} args
       → x < n
       → validTerm n (var x args)

  var2 : ∀ {x} args
       → ¬ (x < n)
       → validTerm n (var x args)

  zero : ∀ {o} args 
       → o ≡ zero'
       → validTerm n (con o args)              
   -- [] would be more precise, but we don't need that

  suc  : ∀ {t v r o} 
       → o ≡ suc'
       → validTerm n t
       → validTerm n (con o (arg v r t ∷ []))

  con : ∀ {o} args
      → o ≢ zero'
      → o ≢ suc'
      → validTerm n (con o args)
  
  op : ∀ {t1 t2 r1 v1 r2 v2 o} 
     → validTerm n t1 
     → validTerm n t2 
     → o ≡ plus' ⊎ o ≡ mult'
     → validTerm n (def o (arg v1 r1 t1 ∷ arg v2 r2 t2 ∷ []))

  def : ∀ {o} args
      → o ≢ plus'
      → o ≢ mult'
      → validTerm n (def o args)

-- a method to differentiate between atomic and arithmetic expressions

data Kind : Set where
  atom arith : Kind

getKind : ∀ {n t} → validTerm n t → Kind
getKind (var1 args x₁)  = arith
getKind (var2 args x₁)  = atom
getKind (zero _ _)      = arith
getKind (suc _ val)     = getKind val
getKind (con args x y)  = atom
getKind (op val val₁ x) = arith
getKind (def args x x₁) = atom

{-
-- validTerm is decidable

validTermDec : ∀ {n} t → Dec (validTerm n t)

validTermDec {n} (var x args) with suc x ≤? n
validTermDec (var x args) | yes p = yes (var1 args p)
validTermDec (var x args) | no ¬p = yes (var2 args ¬p)

validTermDec (con c args) with c ≟-Name zero'
validTermDec (con c args) | yes p = yes (zero args p)
validTermDec (con c args) | no ¬p with c ≟-Name suc'
validTermDec (con c []) | no ¬p | yes p = 
  no (λ { (zero .[] x) → ¬p x ; (con .[] x x₁) → x₁ p })
validTermDec {n} (con c (arg v r x ∷ [])) | no ¬p | yes p 
  with validTermDec {n} x
validTermDec (con c (arg v r x ∷ [])) | no ¬p | yes p₁ | yes p = yes (suc p₁ p)
validTermDec (con c (arg v r x ∷ [])) | no ¬p₁ | yes p | no ¬p = 
  no (λ { (zero .(arg v r x ∷ []) x₁) → ¬p₁ x₁ ; (suc x₁ x₂) → ¬p x₂ ; (con .(arg v r x ∷ []) x₁ x₂) → x₂ p })
validTermDec (con c (x ∷ x₁ ∷ args)) | no ¬p | yes p 
  = no (λ { (zero .(x ∷ x₁ ∷ args) x₂) → ¬p x₂ ; (con .(x ∷ x₁ ∷ args) x₂ x₃) → x₃ p })
validTermDec (con c args) | no ¬p₁ | no ¬p = yes (con args ¬p₁ ¬p)

validTermDec (def f args) with f ≟-Name plus'
validTermDec (def f []) | yes p = no (λ { (def .[] x x₁) → x p })
validTermDec (def f (x ∷ [])) | yes p = no (λ { (def .(x ∷ []) x₁ x₂) → x₁ p })
validTermDec {n} (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | yes p with validTermDec {n} x | validTermDec {n} x₁ 
validTermDec (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | yes p₂ | yes p | yes p₁ = {!!}
validTermDec (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | yes p₁ | yes p | no ¬p = {!!}
validTermDec (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | yes p | no ¬p | r2 = {!!}
validTermDec (def f (x ∷ x₁ ∷ x₂ ∷ args)) | yes p = no (λ { (def .(x ∷ x₁ ∷ x₂ ∷ args) x₃ x₄) → x₃ p })
validTermDec (def f args) | no ¬p = {!!}

validTermDec (lam v t) = no (λ ())
validTermDec (pi t₁ t₂) = no (λ ())
validTermDec (sort x) = no (λ ())
validTermDec unknown = no (λ ())
-}

-- something simpler to implement and use than validTermDec as it performs only essential computations

isValid : {n : ℕ} → Term → Bool
isValid (var x args) = true

isValid (con c args) with c ≟-Name zero'
isValid (con c args) | yes p = true
isValid (con c args) | no ¬p with c ≟-Name suc'
isValid (con c []) | no ¬p | yes p = false
isValid (con c (x ∷ x₁ ∷ args))      | no ¬p  | yes p = false
isValid {n} (con c (arg v r x ∷ [])) | no ¬p  | yes p = isValid {n} x
isValid (con c args)                 | no ¬p₁ | no ¬p = true

isValid (def f args) with f ≟-Name plus'
isValid (def f []) | yes p = false
isValid (def f (x ∷ [])) | yes p = false
isValid (def f (x ∷ x₁ ∷ x₂ ∷ args)) | yes p = false
isValid {n} (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | yes p = isValid {n} x ∧ isValid {n} x₁
isValid (def f args) | no ¬p with f ≟-Name mult'
isValid (def f []) | no ¬p | yes p = false
isValid (def f (x ∷ [])) | no ¬p | yes p = false
isValid (def f (x ∷ x₁ ∷ x₂ ∷ args)) | no ¬p | yes p = false
isValid {n} (def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])) | no ¬p | yes p = isValid {n} x ∧ isValid {n} x₁
isValid (def f args) | no ¬p₁ | no ¬p = true

isValid (lam v t) = false
isValid (pi t₁ t₂) = false
isValid (sort x) = false
isValid unknown = false

-- a way to turn computation into a proof 

isValid-sound : ∀ {n} {t} → isValid {n} t ≡ true → validTerm n t
isValid-sound {n} {var x args} val with suc x ≤? n
... | yes p = var1 args p
... | no ¬p = var2 args ¬p

isValid-sound {n} {con c args} val with c ≟-Name zero'
isValid-sound {n} {con c args} val | yes p = zero args p
isValid-sound {n} {con c args} val | no ¬p with c ≟-Name suc'
isValid-sound {n} {con c []} () | no ¬p | yes p
isValid-sound {n} {con c (x ∷ x₁ ∷ args)} () | no ¬p | yes p
isValid-sound {n} {con c (arg v r x ∷ [])} val | no ¬p | yes p = suc p (isValid-sound {n} {x} val)
isValid-sound {n} {con c args} val | no ¬p₁ | no ¬p = con args ¬p₁ ¬p

isValid-sound {n} {def f args} val with f ≟-Name plus'
isValid-sound {n} {def f []} () | yes p
isValid-sound {n} {def f (x ∷ [])} () | yes p
isValid-sound {n} {def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])} val | yes p 
  = op (isValid-sound {n} {x} (and-l val)) (isValid-sound {n} {x₁} (and-r (isValid x) (isValid x₁) val)) (inj₁ p)
isValid-sound {n} {def f (x ∷ x₁ ∷ x₂ ∷ args)} () | yes p
isValid-sound {n} {def f args} val | no ¬p with f ≟-Name mult'
isValid-sound {n} {def f []} () | no ¬p | yes p
isValid-sound {n} {def f (x ∷ [])} () | no ¬p | yes p
isValid-sound {n} {def f (arg v r x ∷ arg v₁ r₁ x₁ ∷ [])} val | no ¬p | yes p 
  = op (isValid-sound {n} {x} (and-l val)) (isValid-sound {n} {x₁} (and-r (isValid x) (isValid x₁) val)) (inj₂ p)
isValid-sound {n} {def f (x ∷ x₁ ∷ x₂ ∷ args)} () | no ¬p | yes p
isValid-sound {n} {def f args} val | no ¬p₁ | no ¬p = def args ¬p₁ ¬p

isValid-sound {n} {lam v t} ()
isValid-sound {n} {pi t₁ t₂} ()
isValid-sound {n} {sort x} ()
isValid-sound {n} {unknown} ()
-}
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
           .(isEquality t ≡ true)
          → Atoms
debugGoal g eq =
  let t = stripPi g in
  let n = argsNo  g in
  distinctAtomsEq {n} (lhs t eq) (rhs t eq) 

debugGoal2 : (g : Term)
          → let t = stripPi g in
           .(isEquality t ≡ true)
          → ∃ (λ k → Polynomial k × Polynomial k)
debugGoal2 g eq =
  let t      = stripPi g in
  let n      = argsNo  g in
  let atomsL = distinctAtomsEq {n} (lhs t eq) (rhs t eq) in
  let m      = length atomsL in
  let atoms  = fromList atomsL in
  (n + m , (term2poly {n} atoms (lhs t eq) , term2poly {n} atoms (rhs t eq)))


-- debugGoalVal : (g : Term)
--           → let t = stripPi g in
--            .(isEquality t ≡ true)
--           → Bool
-- debugGoalVal g eq =
--   let t = stripPi g in
--   let n = argsNo  g in
--   isValid {n} (lhs t eq) ∧ isValid {n} (rhs t eq)

-------------------------------------------
--  Extracting the polynomial structure  --
-------------------------------------------

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

-- The main reflection helper.
-- Takes a term that is known to have the structure of a polynomial and
-- reflects its structure.
{-
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
-}
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
unit-test-3 = quoteGoal g in {!debugGoal2 g!}

unit-test-4 : ∀ n m → n + m + pred n + pred m ≡ pred m + pred n + n + m
unit-test-4 = quoteGoal g in {!debugGoal2 g!}
