module Data.Rational.Make where

open import Data.Empty
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

suc-pred-id : (n : ℕ) → n ≢ 0 → suc (pred n) ≡ n
suc-pred-id zero    ≢0 = ⊥-elim (≢0 refl)
suc-pred-id (suc n) ≢0 = refl

make-coprime : ∀ {s p q} → q ≢ 0 → Coprime p q → Coprime ∣ s ◃ p ∣ (suc (pred q))
make-coprime {s} {p} {q} ≢0 c {i} (divides q₁ eq₁ , divides q₂ eq₂)
  = c {i} ( divides q₁ (sym (abs-◃ s p) ⟨ trans ⟩ eq₁)
          , divides q₂ (sym (suc-pred-id q ≢0) ⟨ trans ⟩ eq₂))

make : ℤ → (q : ℕ) → q ≢ 0 → ℚ
make p q ≢0 with ∣ p ∣ | q | gcd′ ∣ p ∣ q
... | .(q₁ *ℕ g) | .(q₂ *ℕ g) | g , gcd-* q₁ q₂ c = sign p ◃ q₁ / pred q₂
                                                  [ make-coprime q₂≢0 c ]
  where
    q₂≢0 : q₂ ≢ 0
    q₂≢0 eq = ≢0 (cong (λ q₂ → q₂ *ℕ g) eq)

make⁺ : ℤ → ℕ → ℚ
make⁺ p q = make p (suc q) (λ ())

_÷_ : ℤ → (q : ℕ) {_ : q ≢ 0} → ℚ
_÷_ p q {≢0} = make p q ≢0

infixl 8 _÷_
