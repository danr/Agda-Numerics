module Data.Rational.Core where

open import Data.Nat
open import Data.Nat.Coprimality
open import Data.Integer hiding (suc)

infix 4 _/_[_]

record ℚ : Set where
  constructor _/_[_]
  field p        : ℤ
        q-1      : ℕ
        .coprime : Coprime ∣ p ∣ (suc q-1)
        
nom : ℚ → ℤ
nom (p / q-1 [ _ ]) = p

den : ℚ → ℕ
den (p / q-1 [ _ ]) = suc q-1

