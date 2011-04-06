open import Data.Product using ( ∃ ; _×_ ; _,_ )
open import Relation.Unary using ( _∈_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Web.Semantic.DL.ABox.Interp using ( Interp ; _,_ ; ⌊_⌋ ; ind ; _*_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox.Interp using ( Δ ; _⊨_≈_ ; ≈-refl ; ≈-sym ; ≈-trans )
open import Web.Semantic.DL.TBox.Interp.Morphism using 
  ( ≲-image ; ≃-image ; ≃-image⁻¹ ; ≲-resp-≈ ; ≃-resp-≈ ; ≃-iso ) renaming 
  ( _≲_ to _≲′_ ; _≃_ to _≃′_ 
  ; ≲-refl to ≲′-refl ; ≲-trans to ≲′-trans
  ; ≃-refl to ≃′-refl ; ≃-sym to ≃′-sym ; ≃-trans to ≃′-trans 
  ; ≃-impl-≲ to ≃-impl-≲′ )
open import Web.Semantic.Util using ( _⊕_⊕_ ; inode )

module Web.Semantic.DL.ABox.Interp.Morphism {Σ : Signature} where

infix 2 _≲_ _≃_ _≋_
infix 5 _**_ 

-- data _≲_ {X} : (I J : Interp Σ X) → Set₁ where
--   _,_ : ∀ {I J i j} (I≲J : I ≲′ J) → 
--     (∀ x → (J ⊨ ≲-image I≲J (i x) ≈ j x)) → 
--       ((I , i) ≲ (J , j))

data _≲_ {X} (I J : Interp Σ X) : Set where
  _,_ : ∀ (I≲J : ⌊ I ⌋ ≲′ ⌊ J ⌋) → 
    (i≲j : ∀ x → (⌊ J ⌋ ⊨ ≲-image I≲J (ind I x) ≈ ind J x)) → 
      (I ≲ J)

≲⌊_⌋ : ∀ {X} {I J : Interp Σ X} → (I ≲ J) → (⌊ I ⌋ ≲′ ⌊ J ⌋)
≲⌊_⌋ (I≲J , i≲j) = I≲J

≲-resp-ind : ∀ {X} {I J : Interp Σ X} → (I≲J : I ≲ J) →
  ∀ x → (⌊ J ⌋ ⊨ ≲-image ≲⌊ I≲J ⌋ (ind I x) ≈ ind J x)
≲-resp-ind (I≲J , i≲j) = i≲j

≲-refl : ∀ {X} (I : Interp Σ X) → (I ≲ I)
≲-refl I = (≲′-refl ⌊ I ⌋ , λ x → ≈-refl ⌊ I ⌋)

≲-trans : ∀ {X} {I J K : Interp Σ X} → (I ≲ J) → (J ≲ K) → (I ≲ K)
≲-trans {X} {I} {J} {K} I≲J J≲K =
  (≲′-trans ≲⌊ I≲J ⌋ ≲⌊ J≲K ⌋ , λ x → ≈-trans ⌊ K ⌋ (≲-resp-≈ ≲⌊ J≲K ⌋ (≲-resp-ind I≲J x)) (≲-resp-ind J≲K x))

_**_ : ∀ {X Y I J} (f : Y → X) → (I ≲ J) → (f * I ≲ f * J)
f ** I≲J = (≲⌊ I≲J ⌋ , λ x → ≲-resp-ind I≲J (f x))

_≋_ : ∀ {X} {I J : Interp Σ X} → (I ≲ J) → (I ≲ J) → Set
_≋_ {X} {I} {J} I≲₁J I≲₂J = ∀ x → (⌊ J ⌋ ⊨ ≲-image ≲⌊ I≲₁J ⌋ x ≈ ≲-image ≲⌊ I≲₂J ⌋ x)

data _≃_ {X} : (I J : Interp Σ X) → Set₁ where
  _,_ : ∀ {I J i j} → (I≃J : I ≃′ J) → 
    (∀ x → (J ⊨ ≃-image I≃J (i x) ≈ j x)) →
      ((I , i) ≃ (J , j))

≃⌊_⌋ : ∀ {X} {I J : Interp Σ X} → (I ≃ J) → (⌊ I ⌋ ≃′ ⌊ J ⌋)
≃⌊_⌋ (I≃J , i≃j) = I≃J

≃-impl-≲ : ∀ {X} {I J : Interp Σ X} → (I ≃ J) → (I ≲ J)
≃-impl-≲ (I≃J , i≃j) = (≃-impl-≲′ I≃J , i≃j)

≃-resp-ind : ∀ {X} {I J : Interp Σ X} → (I≃J : I ≃ J) →
  ∀ x → (⌊ J ⌋ ⊨ ≃-image ≃⌊ I≃J ⌋ (ind I x) ≈ ind J x)
≃-resp-ind (I≃J , i≃j) = i≃j

≃-resp-ind⁻¹ : ∀ {X} {I J : Interp Σ X} → (I≃J : I ≃ J) →
  ∀ x → (⌊ I ⌋ ⊨ ≃-image⁻¹ ≃⌊ I≃J ⌋ (ind J x) ≈ ind I x)
≃-resp-ind⁻¹ {X} {I , i} {J , j} (I≃J , i≃j) x =
  ≈-trans I (≃-resp-≈ (≃′-sym I≃J) (≈-sym J (i≃j x))) (≃-iso I≃J (i x))

≃-refl : ∀ {X} (I : Interp Σ X) → (I ≃ I)
≃-refl (I , i) = (≃′-refl I , λ x → ≈-refl I)

≃-symm : ∀ {X} {I J : Interp Σ X} → (I ≃ J) → (J ≃ I)
≃-symm {X} {I , i} {J , j} (I≃J , i≃j) =
  (≃′-sym I≃J , ≃-resp-ind⁻¹ {X} {I , i} {J , j} (I≃J , i≃j))

≃-trans : ∀ {X} {I J K : Interp Σ X} → (I ≃ J) → (J ≃ K) → (I ≃ K)
≃-trans {X} {I , i} {J , j} {K , k} (I≃J , i≃j) (J≃K , j≃k) =
  (≃′-trans I≃J J≃K , λ x → ≈-trans K (≃-resp-≈ J≃K (i≃j x)) (j≃k x))
