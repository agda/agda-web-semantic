open import Data.Product using ( ∃ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.TBox.Interp using
  ( Interp ; Δ ; _⊨_≈_ ; con ; rol ; ≈-refl ; ≈-sym ; ≈-trans ; con-≈ ; rol-≈ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.Util using ( id ; _∘_ )

module Web.Semantic.DL.TBox.Interp.Morphism {Σ : Signature} where

infix 2 _≲_ _≃_

-- I ≲ J whenever J respects all the properties of I

data _≲_ (I J : Interp Σ) : Set where
  morph :
    (f : Δ I → Δ J) →
    (≲-resp-≈ : ∀ {x y} → (I ⊨ x ≈ y) → (J ⊨ f x ≈ f y)) →
    (≲-resp-con : ∀ {c x} → (x ∈ con I c) → (f x ∈ con J c)) →
    (≲-resp-rol : ∀ {r x y} → ((x , y) ∈ rol I r) → ((f x , f y) ∈ rol J r)) →
    (I ≲ J)
  
≲-image : ∀ {I J} → (I ≲ J) → Δ I → Δ J
≲-image (morph f ≲-resp-≈ ≲-resp-con ≲-resp-rol) = f

≲-image² : ∀ {I J} → (I ≲ J) → (Δ I × Δ I) → (Δ J × Δ J)
≲-image² I≲J (x , y) = (≲-image I≲J x , ≲-image I≲J y)

≲-resp-≈ : ∀ {I J} → (I≲J : I ≲ J) → ∀ {x y} → (I ⊨ x ≈ y) →
  (J ⊨ ≲-image I≲J x ≈ ≲-image I≲J y)
≲-resp-≈ (morph f ≲-resp-≈ ≲-resp-con ≲-resp-rol) = ≲-resp-≈

≲-resp-con : ∀ {I J} → (I≲J : I ≲ J) → ∀ {c x} → (x ∈ con I c) → 
  (≲-image I≲J x ∈ con J c)
≲-resp-con (morph f ≲-resp-≈ ≲-resp-con ≲-resp-rol) = ≲-resp-con

≲-resp-rol : ∀ {I J} → (I≲J : I ≲ J) → ∀ {r xy} → (xy ∈ rol I r) → 
  (≲-image² I≲J xy ∈ rol J r)
≲-resp-rol (morph f ≲-resp-≈ ≲-resp-con ≲-resp-rol) {r} {x , y} = ≲-resp-rol

≲-refl : ∀ I → (I ≲ I)
≲-refl I = morph id id id id

≲-trans : ∀ {I J K} → (I ≲ J) → (J ≲ K) → (I ≲ K)
≲-trans I≲J J≲K = morph 
  (≲-image J≲K ∘ ≲-image I≲J) 
  (≲-resp-≈ J≲K ∘ ≲-resp-≈ I≲J) 
  (≲-resp-con J≲K ∘ ≲-resp-con I≲J)
  (≲-resp-rol J≲K ∘ ≲-resp-rol I≲J)

-- I ≃ J whenever there is an isomprhism between I and J

data _≃_ (I J : Interp Σ) : Set where
  iso :
    (≃-impl-≲ : I ≲ J) →
    (≃-impl-≳ : J ≲ I) →
    (≃-iso : ∀ x → I ⊨ (≲-image ≃-impl-≳ (≲-image ≃-impl-≲ x)) ≈ x) →
    (≃-iso⁻¹ : ∀ x → J ⊨ (≲-image ≃-impl-≲ (≲-image ≃-impl-≳ x)) ≈ x) →
    (I ≃ J)

≃-impl-≲ : ∀ {I J} → (I ≃ J) → (I ≲ J)
≃-impl-≲ (iso ≃-impl-≲ ≃-impl-≳ ≃-iso ≃-iso⁻¹) = ≃-impl-≲

≃-impl-≳ : ∀ {I J} → (I ≃ J) → (J ≲ I)
≃-impl-≳ (iso ≃-impl-≲ ≃-impl-≳ ≃-iso ≃-iso⁻¹) = ≃-impl-≳

≃-image : ∀ {I J} → (I ≃ J) → Δ I → Δ J
≃-image I≃J = ≲-image (≃-impl-≲ I≃J)

≃-image² : ∀ {I J} → (I ≃ J) → (Δ I × Δ I) → (Δ J × Δ J)
≃-image² I≃J = ≲-image² (≃-impl-≲ I≃J)

≃-image⁻¹ : ∀ {I J} → (I ≃ J) → Δ J → Δ I
≃-image⁻¹ I≃J = ≲-image (≃-impl-≳ I≃J)

≃-image²⁻¹ : ∀ {I J} → (I ≃ J) → (Δ J × Δ J) → (Δ I × Δ I)
≃-image²⁻¹ I≃J = ≲-image² (≃-impl-≳ I≃J)

≃-iso : ∀ {I J} → (I≃J : I ≃ J) → ∀ x → (I ⊨ (≃-image⁻¹ I≃J (≃-image I≃J x)) ≈ x)
≃-iso (iso ≃-impl-≲ ≃-impl-≳ ≃-iso ≃-iso⁻¹) = ≃-iso

≃-iso⁻¹ : ∀ {I J} → (I≃J : I ≃ J) → ∀ x → (J ⊨ (≃-image I≃J (≃-image⁻¹ I≃J x)) ≈ x)
≃-iso⁻¹ (iso ≃-impl-≲ ≃-impl-≳ ≃-iso ≃-iso⁻¹) = ≃-iso⁻¹

≃-resp-≈ : ∀ {I J} → (I≃J : I ≃ J) → ∀ {x y} →
  (I ⊨ x ≈ y) → (J ⊨ ≃-image I≃J x ≈ ≃-image I≃J y)
≃-resp-≈ I≃J = ≲-resp-≈ (≃-impl-≲ I≃J)

≃-refl-≈ : ∀ {I J} → (I≃J : I ≃ J) → ∀ {x y} →
  (I ⊨ ≃-image⁻¹ I≃J x ≈ ≃-image⁻¹ I≃J y) → (J ⊨ x ≈ y)
≃-refl-≈ {I} {J} I≃J {x} {y} x≈y = 
  ≈-trans J (≈-sym J (≃-iso⁻¹ I≃J x)) 
    (≈-trans J (≃-resp-≈ I≃J x≈y) (≃-iso⁻¹ I≃J y))

≃-refl : ∀ I → (I ≃ I)
≃-refl I = iso (≲-refl I) (≲-refl I) (λ x → ≈-refl I) (λ x → ≈-refl I)

≃-sym : ∀ {I J} → (I ≃ J) → (J ≃ I)
≃-sym I≃J = iso (≃-impl-≳ I≃J) (≃-impl-≲ I≃J) (≃-iso⁻¹ I≃J) (≃-iso I≃J)

≃-trans : ∀ {I J K} → (I ≃ J) → (J ≃ K) → (I ≃ K)
≃-trans {I} {J} {K} I≃J J≃K = iso 
  (≲-trans (≃-impl-≲ I≃J) (≃-impl-≲ J≃K)) 
  (≲-trans (≃-impl-≳ J≃K) (≃-impl-≳ I≃J)) 
  (λ x → ≈-trans I (≲-resp-≈ (≃-impl-≳ I≃J) (≃-iso J≃K (≃-image I≃J x)))
    (≃-iso I≃J x)) 
  (λ x → ≈-trans K (≲-resp-≈ (≃-impl-≲ J≃K) (≃-iso⁻¹ I≃J (≃-image⁻¹ J≃K x)))
    (≃-iso⁻¹ J≃K x))
