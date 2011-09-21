module Data.Rational.Lemmas where

open import Data.Integer renaming (_*_ to _*ℤ_ ; suc to ℤsuc ; pred to ℤpred)
open import Data.Nat     renaming (_*_ to _*ℕ_)
open import Data.Nat.Coprimality hiding (sym)
open import Data.Nat.Divisibility
open import Data.Product
open import Data.Sign

open import Data.Integer.Properties
open import Function

open import Relation.Binary.PropositionalEquality

open import Data.Rational.Core
open import Data.Rational.Make

make-lemma : (p₁ p₂ : ℤ) (q₁ q₂ : ℕ) → p₁ ≡ p₂ → q₁ ≡ q₂ → (q₁≢0 : q₁ ≢ 0) (q₂≢0 : q₂ ≢ 0)
           → make p₁ q₁ q₁≢0 ≡ make p₂ q₂ q₂≢0
make-lemma p .p q .q refl refl q₁≢0 q₂≢0 with ∣ p ∣ | q | gcd′ ∣ p ∣ q
... | .(q₁ *ℕ g) | .(q₂ *ℕ g) | g , gcd-* q₁ q₂ c = refl 

