{-# OPTIONS --universe-polymorphism #-}
open import Relation.Binary

module Algebra.HomomorphicRepresentations
       {i j}
       (U : Set i)           -- the "desired" representation, yet without properties
       (⟨U⟩ : Set j)         -- the "alternative" representation, with properties
       (inject : U → ⟨U⟩)    -- inject to the alternative representation
       (extract : ⟨U⟩ → U)   -- extract from the alternative representation
       (_≈_ : Rel U i)
       (_≈′_ : Rel ⟨U⟩ j)
       (inv : (u : U) → u ≈ extract (inject u))
       (resp : {u v : ⟨U⟩} → u ≈′ v → extract u ≈ extract v)
       (≈-isEquivalence : IsEquivalence _≈_)
       where

open IsEquivalence ≈-isEquivalence
  renaming (refl to ≈-refl ; sym to ≈-sym ; trans to ≈-trans)

import Relation.Binary.EqReasoning as Eq
open Eq (record { Carrier = U
                ; _≈_ = _≈_
                ; isEquivalence = ≈-isEquivalence})

open import Algebra.FunctionProperties.Core
open import Algebra.Structures
open import Algebra.Morphism

open import Function

open import Data.Product using (_,_ ; proj₁ ; proj₂)

import Algebra.FunctionProperties as FP; open FP _≈_

open Definitions ⟨U⟩ U _≈_

module Semigroups
       (_+_ : Op₂ U)
       (_+′_ : Op₂ ⟨U⟩)
       (+-extract : Homomorphic₂ extract _+′_ _+_)
       (+-cong    : _+_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_) where
       
  SemigroupRepr : IsSemigroup _≈′_ _+′_ → IsSemigroup _≈_ _+_
  SemigroupRepr isSemigroup = record
      { isEquivalence = ≈-isEquivalence
      ; assoc = +-assoc
      ; ∙-cong = +-cong
      }
    where
      open IsSemigroup isSemigroup
      
      +-assoc : Associative _+_
      +-assoc x y z = begin
          (x + y) + z                                                    ≈⟨ (inv x ⟨ +-cong ⟩ inv y) ⟨ +-cong ⟩ inv z ⟩
          (extract (inject x) + extract (inject y)) + extract (inject z) ≈⟨ ≈-sym (+-extract _ _) ⟨ +-cong ⟩ ≈-refl ⟩
          extract (inject x +′ inject y) + extract (inject z)            ≈⟨ ≈-sym (+-extract _ _) ⟩
          extract ((inject x +′ inject y) +′ inject z)                   ≈⟨ resp (assoc _ _ _) ⟩
          extract (inject x +′ (inject y +′ inject z))                   ≈⟨ +-extract _ _ ⟩
          extract (inject x) + extract (inject y +′ inject z)            ≈⟨ ≈-refl ⟨ +-cong ⟩ +-extract _ _ ⟩
          extract (inject x) + (extract (inject y) + extract (inject z)) ≈⟨ ≈-sym (inv x ⟨ +-cong ⟩ (inv y ⟨ +-cong ⟩ inv z)) ⟩
          x + (y + z)
        ∎
        
  module Monoids (#0 : U)
                 (⟨0⟩ : ⟨U⟩)
                 (0-extract : Homomorphic₀ extract ⟨0⟩ #0) where

    MonoidRepr : IsMonoid _≈′_ _+′_ ⟨0⟩ → IsMonoid _≈_ _+_ #0
    MonoidRepr isMonoid = record
        { isSemigroup = SemigroupRepr isSemigroup
        ; identity = left , right
        }
      where
        open IsMonoid isMonoid
        left : LeftIdentity #0 _+_
        left x = begin
            #0 + x                           ≈⟨ ≈-sym 0-extract ⟨ +-cong ⟩ inv x ⟩
            extract ⟨0⟩ + extract (inject x) ≈⟨ ≈-sym (+-extract _ _) ⟩
            extract (⟨0⟩ +′ inject x)        ≈⟨ resp (proj₁ identity _) ⟩
            extract (inject x)               ≈⟨ ≈-sym (inv x) ⟩
            x
          ∎

        right : RightIdentity #0 _+_
        right x = begin
            x + #0                           ≈⟨ inv x ⟨ +-cong ⟩ ≈-sym 0-extract ⟩
            extract (inject x) + extract ⟨0⟩ ≈⟨ ≈-sym (+-extract _ _) ⟩
            extract (inject x +′ ⟨0⟩)        ≈⟨ resp (proj₂ identity _) ⟩
            extract (inject x)               ≈⟨ ≈-sym (inv x) ⟩
            x
          ∎ 


    CommutativeMonoidRepr : IsCommutativeMonoid _≈′_ _+′_ ⟨0⟩ → IsCommutativeMonoid _≈_ _+_ #0
    CommutativeMonoidRepr isCommutativeMonoid = record
        { isSemigroup = SemigroupRepr isSemigroup
        ; identityˡ = proj₁ (IsMonoid.identity (MonoidRepr isMonoid))
        ; comm = +-comm
        }
      where
        open IsCommutativeMonoid isCommutativeMonoid

        +-comm : Commutative _+_
        +-comm x y = begin
            x + y                                   ≈⟨ +-cong (inv x) (inv y) ⟩
            extract (inject x) + extract (inject y) ≈⟨ ≈-sym (+-extract _ _) ⟩
            extract (inject x +′ inject y)          ≈⟨ resp (comm _ _) ⟩
            extract (inject y +′ inject x)          ≈⟨ +-extract _ _ ⟩
            extract (inject y) + extract (inject x) ≈⟨ ≈-sym (+-cong (inv y) (inv x)) ⟩
            y + x
          ∎

    module Groups (-_ : Op₁ U)
                  (-′_ : Op₁ ⟨U⟩)
                  (neg-extract : Homomorphic₁ extract -′_ -_) 
                  (neg-cong    : -_ Preserves _≈_ ⟶ _≈_) where
      GroupRepr : IsGroup _≈′_ _+′_ ⟨0⟩ -′_ → IsGroup _≈_ _+_ #0 -_
      GroupRepr isGroup = record
          { isMonoid = MonoidRepr isMonoid
          ; inverse  = left , right
          ; ⁻¹-cong  = neg-cong
          }
        where
          open IsGroup isGroup

          left : LeftInverse #0 -_ _+_
          left x = begin
              (- x) + x                                   ≈⟨ neg-cong (inv x) ⟨ +-cong ⟩ inv x ⟩
              (- extract (inject x)) + extract (inject x) ≈⟨ ≈-sym (neg-extract _) ⟨ +-cong ⟩ ≈-refl ⟩
              extract (-′ inject x) + extract (inject x)  ≈⟨ ≈-sym (+-extract _ _) ⟩
              extract ((-′ inject x) +′ inject x)         ≈⟨ resp (proj₁ inverse _) ⟩
              extract ⟨0⟩                                 ≈⟨ 0-extract ⟩
              #0
            ∎
            
          right : RightInverse #0 -_ _+_
          right x = begin
              x + (- x)                                   ≈⟨ inv x ⟨ +-cong ⟩ neg-cong (inv x) ⟩
              extract (inject x) + (- extract (inject x)) ≈⟨ ≈-sym (≈-refl ⟨ +-cong ⟩ neg-extract _) ⟩
              extract (inject x) + extract (-′ inject x)  ≈⟨ ≈-sym (+-extract _ _) ⟩
              extract (inject x +′ (-′ inject x))         ≈⟨ resp (proj₂ inverse _) ⟩
              extract ⟨0⟩                                 ≈⟨ 0-extract ⟩
              #0
            ∎
            
      AbelianGroupRepr : IsAbelianGroup _≈′_ _+′_ ⟨0⟩ -′_ → IsAbelianGroup _≈_ _+_ #0 -_
      AbelianGroupRepr isAbelianGroup = record
          { isGroup = GroupRepr isGroup
          ; comm    = IsCommutativeMonoid.comm (CommutativeMonoidRepr isCommutativeMonoid)
          }
        where
          open IsAbelianGroup isAbelianGroup

    open Groups public
    
  open Monoids public
  
open Semigroups public

-- TODO : Investigate if this is better with records          
module Rings 
       (_+_ _*_ : Op₂ U)
       (_+′_ _*′_ : Op₂ ⟨U⟩)
       (+-extract : Homomorphic₂ extract _+′_ _+_)
       (*-extract : Homomorphic₂ extract _*′_ _*_)
       (+-cong    : _+_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_)
       (*-cong    : _*_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_)       
       (#0 #1 : U)
       (⟨0⟩ ⟨1⟩ : ⟨U⟩)
       (0-extract : Homomorphic₀ extract ⟨0⟩ #0)
       (1-extract : Homomorphic₀ extract ⟨1⟩ #1)
       (-_ : Op₁ U)
       (-′_ : Op₁ ⟨U⟩)
       (neg-extract : Homomorphic₁ extract -′_ -_) 
       (neg-cong    : -_ Preserves _≈_ ⟶ _≈_) where
       
  RingRepr : IsRing _≈′_ _+′_ _*′_ -′_ ⟨0⟩ ⟨1⟩ → IsRing _≈_ _+_ _*_ -_ #0 #1
  RingRepr isRing = record
      { +-isAbelianGroup = AbelianGroupRepr _+_ _+′_ +-extract +-cong
                                            #0 ⟨0⟩ 0-extract
                                            -_ -′_ neg-extract neg-cong
                                            +-isAbelianGroup
      ; *-isMonoid = MonoidRepr _*_ _*′_ *-extract *-cong
                                 #1 ⟨1⟩ 1-extract
                                 *-isMonoid
      ; distrib = left , right
      }
    where
      open IsRing isRing

      left : _*_ DistributesOverˡ _+_
      left x y z = begin
          x * (y + z)                                                     ≈⟨ inv x ⟨ *-cong ⟩ (inv y ⟨ +-cong ⟩ inv z) ⟩
          extract (inject x) * (extract (inject y) + extract (inject z))  ≈⟨ ≈-refl ⟨ *-cong ⟩ ≈-sym (+-extract _ _) ⟩
          extract (inject x) * extract (inject y +′ inject z)             ≈⟨ ≈-sym (*-extract _ _) ⟩
          extract (inject x *′ (inject y +′ inject z))                    ≈⟨ resp (proj₁ distrib _ _ _) ⟩
          extract ((inject x *′ inject y) +′ (inject x *′ inject z))      ≈⟨ +-extract _ _ ⟩
          extract (inject x *′ inject y) + extract (inject x *′ inject z) ≈⟨ *-extract _ _ ⟨ +-cong ⟩ *-extract _ _ ⟩
          (extract (inject x) * extract (inject y)) +
            (extract (inject x) * extract (inject z))                     ≈⟨ ≈-sym ((inv x ⟨ *-cong ⟩ inv y) ⟨ +-cong ⟩ (inv x ⟨ *-cong ⟩ inv z)) ⟩
          (x * y) + (x * z)
        ∎

      right : _*_ DistributesOverʳ _+_
      right x y z = begin
          (y + z) * x                                                     ≈⟨ (inv y ⟨ +-cong ⟩ inv z) ⟨ *-cong ⟩ inv x ⟩
          (extract (inject y) + extract (inject z)) * extract (inject x)  ≈⟨ ≈-sym (+-extract _ _) ⟨ *-cong ⟩ ≈-refl ⟩
          extract (inject y +′ inject z) * extract (inject x)             ≈⟨ ≈-sym (*-extract _ _) ⟩
          extract ((inject y +′ inject z) *′ inject x)                    ≈⟨ resp (proj₂ distrib _ _ _) ⟩
          extract ((inject y *′ inject x) +′ (inject z *′ inject x))      ≈⟨ +-extract _ _ ⟩
          extract (inject y *′ inject x) + extract (inject z *′ inject x) ≈⟨ *-extract _ _ ⟨ +-cong ⟩ *-extract _ _ ⟩
          (extract (inject y) * extract (inject x)) +
            (extract (inject z) * extract (inject x))                     ≈⟨ ≈-sym ((inv y ⟨ *-cong ⟩ inv x) ⟨ +-cong ⟩ (inv z ⟨ *-cong ⟩ inv x)) ⟩
          (y * x) + (z * x)
        ∎
     
  CommutativeRingRepr : IsCommutativeRing _≈′_ _+′_ _*′_ -′_ ⟨0⟩ ⟨1⟩ → IsCommutativeRing _≈_ _+_ _*_ -_ #0 #1
  CommutativeRingRepr isCommutativeRing = record
      { isRing = RingRepr isRing
      ; *-comm = IsCommutativeMonoid.comm
                   (CommutativeMonoidRepr _*_ _*′_ *-extract *-cong
                                          #1 ⟨1⟩ 1-extract
                                          *-isCommutativeMonoid)
      }
    where
      open IsCommutativeRing isCommutativeRing
      
