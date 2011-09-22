module Data.Rational.Operations where

open import Data.Integer renaming (_+_ to _+ℤ_ ; _*_ to _*ℤ_ ; suc to ℤsuc ; pred to ℤpred)
open import Data.Nat     renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_)

open import Data.Rational.Core
open import Data.Rational.Make

open import Relation.Binary.PropositionalEquality

infixl 6 _+_

_+_ : ℚ → ℚ → ℚ
(p₁ / q₁-1 [ _ ]) + (p₂ / q₂-1 [ _ ]) = make⁺ (p₁ *ℤ + q₂ +ℤ p₂ *ℤ + q₁)
                                             (pred (q₁ *ℕ q₂))
  where 
    q₁ = suc q₁-1    
    q₂ = suc q₂-1

_*_ : ℚ → ℚ → ℚ
(p₁ / q₁-1 [ _ ]) * (p₂ / q₂-1 [ _ ]) = make⁺ (p₁ *ℤ p₂)
                                             (pred (q₁ *ℕ q₂))
                
  where
    q₁ = suc q₁-1   
    q₂ = suc q₂-1

