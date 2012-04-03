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


-- debugGoalVal : (g : Term)
--           → let t = stripPi g in
--            .(isEquality t ≡ true)
--           → Bool
-- debugGoalVal g eq =
--   let t = stripPi g in
--   let n = argsNo  g in
--   isValid {n} (lhs t eq) ∧ isValid {n} (rhs t eq)

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
{-
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
-}
{-

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
isEquality (lam v t)    = false
isEquality (pi t₁ t₂)   = false
isEquality (sort x)     = false
isEquality unknown      = false

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

------------------------------------------------------
--  Less principled approach to lhs,rhs extraction  --
------------------------------------------------------

-}

{-
debugGoal : (g : Term)
          → let t = stripPi g in
           .(isEquality t ≡ true)
          → Atoms
debugGoal g eq =
  let t = stripPi g in
  let n = argsNo  g in
  distinctAtomsEq {n} (lhs t eq) (rhs t eq) 
-}
