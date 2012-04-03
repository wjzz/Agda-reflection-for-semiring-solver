{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)

  2012-04-01

  A demonstration of the functions defined in SolverFrontend.
-}
module Demo where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec renaming (reverse to vreverse)
open import Relation.Binary.PropositionalEquality

-- semiring solver and reflection

open SemiringSolver
open import Data.Vec.N-ary
open import Reflection
open import SolverFrontend

-----------------------------------------------------
--  Demonstration of the various solver functions  --
-----------------------------------------------------

-- We show a few ways to solve the same arithmetic goal.


-- The original version from the stdlib. It doesn't use the Reflection API.
-- We basically have to write the same equation in two notations.

stdlib : ∀ m n → suc (m + n + (m + n)) ≡ m + m + suc (n + n)
stdlib = solve 2 (λ m n → con 1 :+ (m :+ n :+ (m :+ n)) := m :+ m :+ (con 1 :+ (n :+ n))) refl

-- A version using the reflection API and our low-level helpers.
-- This time we don't have to rewrite the goal, but
-- we need to build the vector of arguments and reverse it as well.
-- 
-- We have so many refls because we need to show that 
-- the precondition in lhs, rhs and term2poly hold.

ugly : ∀ m n → suc (m + n + (m + n)) ≡ m + m + suc (n + n)
ugly m n = quoteGoal e in prove (n ∷ m ∷ []) 
                            (term2poly (lhs e refl) refl)
                            (term2poly (rhs e refl) refl) 
                             refl

-- This is basically the same as above, but encapsulated in a function.
-- If we get rid of the explicit vector we'll be good.

wrapped : ∀ m n → suc (m + n + (m + n)) ≡ m + m + suc (n + n)
wrapped m n = quoteGoal e in kill e (n ∷ m ∷ []) refl refl refl refl

-- Transitive step, uses more helpers to calculate the number of
-- variables automatically (it was infered from the vectors length above)
-- The lambdas need to be moved inwards.

calculating : ∀ m n → suc (m + n + (m + n)) ≡ m + m + suc (n + n)
calculating = quoteGoal e in λ m n → kil2 e (n ∷ m ∷ []) refl refl refl refl
  
-- Final version, uses solve rather than prove internally, therefore
-- there are no vectors popping up.
-- The refls look a bit silly, but this wrapper can used as a tactic: 
-- to solve any goal [solvable by the semiring solver] 
-- simply copy-paste 'quoteGoal e in solv e refl refl refl refl' and worry no more ;-)

notbad : ∀ m n → suc (m + n + (m + n)) ≡ m + m + suc (n + n)
notbad = quoteGoal e in ring e refl refl refl refl

-- Unsafe version for the lazy - uses trustMe to eliminate 3 out of 4 refls.
-- It seems that the final one can't be dealt with this way.

unsafe : ∀ m n → suc (m + n + (m + n)) ≡ m + m + suc (n + n)
unsafe = quoteGoal e in solv' e refl

-------------------------------
--  More tests and examples  --
-------------------------------

ex-0 : ∀ m n → m + n ≡ n + m
ex-0 = quoteGoal e in ring e refl refl refl refl

ex-1 : ∀ m n k → m + n + (suc k) ≡ k + m + 1 + n
ex-1 = quoteGoal e in ring e refl refl refl refl

ex-3 : ∀ m → 5 * m ≡ m + m + m + m + m
ex-3 = quoteGoal e in ring e refl refl refl refl

------------------
--  Comparison  --
------------------

shuffle-test2 : (a b c : ℕ) → a + b + 2 + c + b ≡ 1 + b * 2 + (c + a) + 1
shuffle-test2 = quoteGoal e in ring e refl refl refl refl


-------------------------------------
--  Examples that do not work yet  --
-------------------------------------

-- a shortcoming of the present approach: we do not deal with
-- non-interpreted constants at all

ex-2 : ℕ → ℕ
ex-2 n = 213 where
  -- wrong, the library doesn't allow non qualified names yet
  
  open import Data.List
  open import Relation.Binary.PropositionalEquality

  lemma : ∀ m → n + m ≡ m + n
  lemma = quoteGoal e in {!e!} 
          {-quoteGoal e in ring e refl refl refl refl
                                        ||
                                this precondition fails
           -} 

postulate
  f : ℕ → ℕ

-- this doesn't work
-- ex-4 : ∀ n m → f n + f m ≡ f m + f n
-- ex-4 = quoteGoal e in ring e refl refl refl refl


-- ugly workaround. works, but we might have as well used the old solve function

ex-5 : ∀ n m → f n + f m ≡ f m + f n
ex-5 n m = lemma (f n) (f m) where

  lemma : ∀ n m → n + m ≡ m + n
  lemma = quoteGoal e in ring e refl refl refl refl

