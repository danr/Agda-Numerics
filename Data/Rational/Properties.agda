module Data.Rational.Properties where

open import Algebra.Structures

open import Data.Integer renaming (_+_ to _+ℤ_ ; _*_ to _*ℤ_ ; suc to ℤsuc ; pred to ℤpred)
open import Data.Nat     renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_)
open import Data.Nat.Coprimality hiding (sym)
open import Data.Nat.Divisibility
open import Data.Product
open import Data.Empty

open import Function

open import Relation.Binary.PropositionalEquality

open import Data.Rational.Core
open import Data.Rational.Lemmas
open import Data.Rational.Make
open import Data.Rational.Operations

import Algebra.FunctionProperties as FP; open FP (_≡_ {A = ℚ})

module ℕ-prop where
  open import Data.Nat.Properties 
  open IsCommutativeSemiring isCommutativeSemiring public

module ℤ-prop where
  open import Data.Integer.Ring
  open IsCommutativeRing isCommutativeRing public

ℚ+comm : Commutative _+_
ℚ+comm (p₁ / q₁-1 [ _ ]) (p₂ / q₂-1 [ _ ]) = make-lemma⁺ p≡ q≡ 
  where
    q₁ = suc q₁-1
    q₂ = suc q₂-1
    
    p≡ : p₁ *ℤ + q₂ +ℤ p₂ *ℤ + q₁ ≡ p₂ *ℤ + q₁ +ℤ p₁ *ℤ + q₂
    p≡ = ℤ-prop.+-comm (p₁ *ℤ + q₂) (p₂ *ℤ + q₁)

    q≡ : pred (q₁ *ℕ q₂) ≡ pred (q₂ *ℕ q₁)
    q≡ = cong pred (ℕ-prop.*-comm q₁ q₂)

-- ℚ+assoc : Associative _+_
-- ℚ+assoc (p₁ / q₁-1 [ _ ]) (p₂ / q₂-1 [ _ ]) (p₃ / q₃-1 [ _ ]) = {!!}

-- (p₁/q₁ + p₂/q₂) + p₃/q₃ = p₁/q₁ + (p₂/q₂ + p₃/q₃)
-- 
-- let p₁₂/q₁2 = (p₁/q₁ + p₂/q₂)
--
-- shorten (a +′ b) = shorten a + shorten b