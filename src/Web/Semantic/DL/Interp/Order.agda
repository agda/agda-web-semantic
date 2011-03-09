open import Data.Product using ( ∃ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.Interp using
  ( Interp ; _⊨_≈_ ; ind ; con ; rol ; ≈-refl ; ≈-sym ; ≈-trans ; con-≈ ; rol-≈ )
open import Web.Semantic.DL.ABox.Signature using ( Signature )
open import Web.Semantic.Util using ( id ; _∘_ )

module Web.Semantic.DL.Interp.Order {Σ : Signature} {Δ : Set} where

-- I ≤ J whenever J respects all the properties of I

record _≤_ (I J : Interp Σ Δ) : Set where
  field
    ≤-resp-≈ : ∀ {x y} → (I ⊨ x ≈ y) → (J ⊨ x ≈ y)
    ≤-resp-ind : ∀ {i} → (J ⊨ ind I i ≈ ind J i)
    ≤-resp-con : ∀ {c x} → (x ∈ con I c) → (x ∈ con J c)
    ≤-resp-rol : ∀ {r x y} → ((x , y) ∈ rol I r) → ((x , y) ∈ rol J r)
  
open _≤_ public

≤-refl : ∀ I → (I ≤ I)
≤-refl I = record
  { ≤-resp-≈ = id
  ; ≤-resp-ind = ≈-refl I
  ; ≤-resp-con = id
  ; ≤-resp-rol = id
  }

≤-trans : ∀ {I J K} → (I ≤ J) → (J ≤ K) → (I ≤ K)
≤-trans {I} {J} {K} I≤J J≤K = record
  { ≤-resp-≈ = ≤-resp-≈ J≤K ∘ ≤-resp-≈ I≤J
  ; ≤-resp-ind = ≈-trans K (≤-resp-≈ J≤K (≤-resp-ind I≤J)) (≤-resp-ind J≤K)
  ; ≤-resp-con = ≤-resp-con J≤K ∘ ≤-resp-con I≤J
  ; ≤-resp-rol = ≤-resp-rol J≤K ∘ ≤-resp-rol I≤J
  }
