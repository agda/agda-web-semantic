open import Data.Product using ( _,_ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.Model.Interp using ( Interp ; Δ ;  _⊨_≈_ ; ind ; con ; rol )
open import Web.Semantic.DL.Signature using ( Signature )

module Web.Semantic.DL.Model.Order {Σ : Signature} {X : Set} where

record _≤_ (I J : Interp Σ X) : Set where
  field
    f : Δ I → Δ J
    ≤-resp-≈ : ∀ {x y} → (I ⊨ x ≈ y) → (J ⊨ f x ≈ f y)
    ≤-resp-ind : ∀ {i x} → (I ⊨ x ≈ ind I i) → (J ⊨ f x ≈ ind J i)
    ≤-resp-con : ∀ {c x} → (x ∈ con I c) → (f x ∈ con J c)
    ≤-resp-rol : ∀ {r x y} → ((x , y) ∈ rol I r) → ((f x , f y) ∈ rol J r)
  
open _≤_ public renaming ( f to image )

≤-refl : ∀ I → (I ≤ I)
≤-refl I = record
  { f = λ x → x
  ; ≤-resp-≈ = λ x≈y → x≈y
  ; ≤-resp-ind = λ x≈⟦i⟧ → x≈⟦i⟧
  ; ≤-resp-con = λ x∈⟦c⟧ → x∈⟦c⟧
  ; ≤-resp-rol = λ xy∈⟦r⟧ → xy∈⟦r⟧
  }

≤-trans : ∀ {I J K} → (I ≤ J) → (J ≤ K) → (I ≤ K)
≤-trans I≤J J≤K = record
  { f = λ x → image J≤K (image I≤J x)
  ; ≤-resp-≈ = λ x≈y → ≤-resp-≈ J≤K (≤-resp-≈ I≤J x≈y)
  ; ≤-resp-ind = λ x≈⟦i⟧ → ≤-resp-ind J≤K (≤-resp-ind I≤J x≈⟦i⟧)
  ; ≤-resp-con = λ x∈⟦c⟧ → ≤-resp-con J≤K (≤-resp-con I≤J x∈⟦c⟧)
  ; ≤-resp-rol = λ xy∈⟦r⟧ → ≤-resp-rol J≤K (≤-resp-rol I≤J xy∈⟦r⟧)
  }
