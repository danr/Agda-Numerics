open import Algebra.Structures
open import Relation.Binary.PropositionalEquality
  renaming (trans to _≡-trans_ ; sym to ≡-sym ; refl to ≡-refl)

module FreePropositionalEquality
       (ℚ ⟨ℚ⟩ : Set)
       (#0 #1 : ℚ)
       (-_ : ℚ → ℚ)
       (_+_ _*_ : ℚ → ℚ → ℚ)

       (⟨0⟩ ⟨1⟩ : ⟨ℚ⟩)
       (⟨-⟩_ : ⟨ℚ⟩ → ⟨ℚ⟩)
       (_⟨+⟩_ _⟨*⟩_ : ⟨ℚ⟩ → ⟨ℚ⟩ → ⟨ℚ⟩)
       (_≈_     : ⟨ℚ⟩ → ⟨ℚ⟩ → Set)
       (isCommutativeRing : IsCommutativeRing _≈_ _⟨+⟩_ _⟨*⟩_ (⟨-⟩_) ⟨0⟩ ⟨1⟩)

       (shorten : ⟨ℚ⟩ → ℚ)
       (inject : ℚ → ⟨ℚ⟩)

       (+-shorten : ∀ x y → shorten x + shorten y ≡ shorten (x ⟨+⟩ y))
       (*-shorten : ∀ x y → shorten x * shorten y ≡ shorten (x ⟨*⟩ y))       
       (≈-cong : ∀ {x y} → x ≈ y → shorten x ≡ shorten y)
       (+-inject  : ∀ x y → inject (x + y) ≈ (inject x ⟨+⟩ inject y))
       (*-inject  : ∀ x y → inject (x * y) ≈ (inject x ⟨*⟩ inject y))
       (0-inject : inject #0 ≈ ⟨0⟩)
       (1-inject : inject #1 ≈ ⟨1⟩)
       (inv : ∀ x → shorten (inject x) ≡ x)
       where

open IsCommutativeRing isCommutativeRing hiding (isEquivalence)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; Σ)

import Algebra.FunctionProperties as FP; open FP (_≡_ {A = ℚ})
open ≡-Reasoning

ℚ-comm-+ : Commutative _+_
ℚ-comm-+ x y = begin
    x + y                                   ≡⟨ cong₂ _+_ (≡-sym (inv x)) (≡-sym (inv y)) ⟩
    shorten (inject x) + shorten (inject y)   ≡⟨ +-shorten (inject x) (inject y) ⟩
    shorten (inject x ⟨+⟩ inject y)         ≡⟨ ≈-cong (+-comm (inject x) (inject y)) ⟩
    shorten (inject y ⟨+⟩ inject x)         ≡⟨ ≡-sym (+-shorten (inject y) (inject x)) ⟩
    shorten (inject y) + shorten (inject x) ≡⟨ cong₂ _+_ (inv y) (inv x) ⟩
    y + x
  ∎ 

ℚ-assoc-+ : Associative _+_
ℚ-assoc-+ x y z = begin
   (x + y) + z                                     ≡⟨ cong₂ _+_ (≡-sym (inv (x + y))) (≡-sym (inv z)) ⟩
   shorten (inject (x + y)) + shorten (inject z)   ≡⟨ +-shorten (inject (x + y)) (inject z) ⟩
   shorten (inject (x + y) ⟨+⟩ inject z)           ≡⟨ ≈-cong (+-cong (+-inject x y) refl) ⟩
   shorten ((inject x ⟨+⟩ inject y) ⟨+⟩ inject z)   ≡⟨ ≈-cong (+-assoc _ _ _) ⟩
   shorten (inject x ⟨+⟩ (inject y ⟨+⟩ inject z))   ≡⟨ ≈-cong (+-cong refl (sym (+-inject y z))) ⟩
   shorten (inject x ⟨+⟩ inject (y + z))           ≡⟨ ≡-sym (+-shorten (inject x) (inject (y + z))) ⟩
   shorten (inject x) + shorten (inject (y + z))   ≡⟨ cong₂ _+_ (inv x) (inv (y + z)) ⟩
   x + (y + z)
 ∎          
  
ℚ-comm-* : Commutative _*_
ℚ-comm-* x y = begin
    x * y                                   ≡⟨ cong₂ _*_ (≡-sym (inv x)) (≡-sym (inv y)) ⟩
    shorten (inject x) * shorten (inject y)   ≡⟨ *-shorten (inject x) (inject y) ⟩
    shorten (inject x ⟨*⟩ inject y)         ≡⟨ ≈-cong (*-comm (inject x) (inject y)) ⟩
    shorten (inject y ⟨*⟩ inject x)         ≡⟨ ≡-sym (*-shorten (inject y) (inject x)) ⟩
    shorten (inject y) * shorten (inject x) ≡⟨ cong₂ _*_ (inv y) (inv x) ⟩
    y * x
  ∎ 


ℚ-assoc-* : Associative _*_
ℚ-assoc-* x y z = begin
   (x * y) * z                                     ≡⟨ cong₂ _*_ (≡-sym (inv (x * y))) (≡-sym (inv z)) ⟩
   shorten (inject (x * y)) * shorten (inject z)   ≡⟨ *-shorten (inject (x * y)) (inject z) ⟩
   shorten (inject (x * y) ⟨*⟩ inject z)           ≡⟨ ≈-cong (*-cong (*-inject x y) refl) ⟩
   shorten ((inject x ⟨*⟩ inject y) ⟨*⟩ inject z)   ≡⟨ ≈-cong (*-assoc _ _ _) ⟩
   shorten (inject x ⟨*⟩ (inject y ⟨*⟩ inject z))   ≡⟨ ≈-cong (*-cong refl (sym (*-inject y z))) ⟩
   shorten (inject x ⟨*⟩ inject (y * z))           ≡⟨ ≡-sym (*-shorten (inject x) (inject (y * z))) ⟩
   shorten (inject x) * shorten (inject (y * z))   ≡⟨ cong₂ _*_ (inv x) (inv (y * z)) ⟩
   x * (y * z)
 ∎          

ℚ-identity-+ : Identity #0 _+_ 
ℚ-identity-+ = (λ x → ℚ-comm-+ #0 x ≡-trans right x) , right
  where
    right : RightIdentity #0 _+_
    right x = begin
        x + #0 ≡⟨ cong₂ _+_ (≡-sym (inv x)) (≡-sym (inv #0) ≡-trans ≈-cong (0-inject)) ⟩
        shorten (inject x) + shorten ⟨0⟩ ≡⟨ +-shorten (inject x) ⟨0⟩ ⟩
        shorten (inject x ⟨+⟩ ⟨0⟩) ≡⟨ ≈-cong (proj₂ +-identity (inject x)) ⟩
        shorten (inject x) ≡⟨ inv x ⟩
        x
      ∎

ℚ-identity-* : Identity #1 _*_ 
ℚ-identity-* = (λ x → ℚ-comm-* #1 x ≡-trans right x) , right
  where
    right : RightIdentity #1 _*_
    right x = begin
        x * #1 ≡⟨ cong₂ _*_ (≡-sym (inv x)) (≡-sym (inv #1) ≡-trans ≈-cong (1-inject)) ⟩
        shorten (inject x) * shorten ⟨1⟩ ≡⟨ *-shorten (inject x) ⟨1⟩ ⟩
        shorten (inject x ⟨*⟩ ⟨1⟩) ≡⟨ ≈-cong (proj₂ *-identity (inject x)) ⟩
        shorten (inject x) ≡⟨ inv x ⟩
        x
      ∎
      
isCR : IsCommutativeRing _≡_ _+_ _*_ -_ #0 #1
isCR = record
  { isRing = record
    { +-isAbelianGroup = record
      { isGroup = record
        { isMonoid = record
          { isSemigroup = record
            { isEquivalence = isEquivalence
            ; assoc = ℚ-assoc-+
            ; ∙-cong = cong₂ _+_
            }
          ; identity = ℚ-identity-+
          }
        ; inverse = {!!}
        ; ⁻¹-cong = cong -_
        }
      ; comm = ℚ-comm-+
      }
    ; *-isMonoid = record
      { isSemigroup = record
        { isEquivalence = isEquivalence
        ; assoc = ℚ-assoc-*
        ; ∙-cong = cong₂ _*_
        }
      ; identity = ℚ-identity-*
      }
    ; distrib = {!!}
    }
  ; *-comm = ℚ-comm-*
  }