open import Data.Product using ( _×_ ; _,_ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.Role using ( Role ; ⟨_⟩ ; ⟨_⟩⁻¹ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox.Interp using ( Interp ; Δ ; rol ; _⊨_≈_ ; rol-≈ ; ≈-refl ; ≈-sym )
open import Web.Semantic.DL.TBox.Interp.Morphism using ( _≲_ ; _≃_ ; ≲-resp-rol ; ≲-image² ; ≃-image ; ≃-image⁻¹ ; ≃-image² ;  ≃-image²⁻¹ ; ≃-impl-≲ ; ≃-iso⁻¹ )
open import Web.Semantic.Util using ( Subset ; _⁻¹ )

module Web.Semantic.DL.Role.Model {Σ : Signature} where

_⟦_⟧₂ : ∀ (I : Interp Σ) → Role Σ → Subset (Δ I × Δ I)
I ⟦ ⟨ r ⟩   ⟧₂ = rol I r
I ⟦ ⟨ r ⟩⁻¹ ⟧₂ = (rol I r)⁻¹

⟦⟧₂-resp-≈ : ∀ I R {w x y z} → 
  (I ⊨ w ≈ x) → ((x , y) ∈ I ⟦ R ⟧₂) → (I ⊨ y ≈ z) → ((w , z) ∈ I ⟦ R ⟧₂) 
⟦⟧₂-resp-≈ I ⟨ r ⟩   w≈x xy∈⟦r⟧ y≈z = rol-≈ I r w≈x xy∈⟦r⟧ y≈z
⟦⟧₂-resp-≈ I ⟨ r ⟩⁻¹ w≈x yx∈⟦r⟧ y≈z = rol-≈ I r (≈-sym I y≈z) yx∈⟦r⟧ (≈-sym I w≈x)

⟦⟧₂-resp-≲ : ∀ {I J : Interp Σ} → (I≲J : I ≲ J) → ∀ {xy} R →
  (xy ∈ I ⟦ R ⟧₂) → (≲-image² I≲J xy ∈ J ⟦ R ⟧₂)
⟦⟧₂-resp-≲ I≲J {x , y} ⟨ r ⟩   xy∈⟦r⟧ = ≲-resp-rol I≲J xy∈⟦r⟧
⟦⟧₂-resp-≲ I≲J {x , y} ⟨ r ⟩⁻¹ yx∈⟦r⟧ = ≲-resp-rol I≲J yx∈⟦r⟧

⟦⟧₂-resp-≃ : ∀ {I J : Interp Σ} → (I≃J : I ≃ J) → ∀ {xy} R →
  (xy ∈ I ⟦ R ⟧₂) → (≃-image² I≃J xy ∈ J ⟦ R ⟧₂)
⟦⟧₂-resp-≃ I≃J = ⟦⟧₂-resp-≲ (≃-impl-≲ I≃J)

⟦⟧₂-refl-≃ : ∀ {I J : Interp Σ} → (I≃J : I ≃ J) → ∀ {xy} R →
  (≃-image²⁻¹ I≃J xy ∈ I ⟦ R ⟧₂) → (xy ∈ J ⟦ R ⟧₂)
⟦⟧₂-refl-≃ {I} {J} I≃J {x , y} R xy∈⟦R⟧ = 
  ⟦⟧₂-resp-≈ J R (≈-sym J (≃-iso⁻¹ I≃J x)) 
    (⟦⟧₂-resp-≃ I≃J R xy∈⟦R⟧) (≃-iso⁻¹ I≃J y)

⟦⟧₂-galois : ∀ {I J : Interp Σ} → (I≃J : I ≃ J) → ∀ {x y} R → 
  ((≃-image⁻¹ I≃J x , y) ∈ I ⟦ R ⟧₂) → ((x , ≃-image I≃J y) ∈ J ⟦ R ⟧₂)
⟦⟧₂-galois {I} {J} I≃J {x} R xy∈⟦R⟧ = 
  ⟦⟧₂-resp-≈ J R (≈-sym J (≃-iso⁻¹ I≃J x)) 
    (⟦⟧₂-resp-≲ (≃-impl-≲ I≃J) R xy∈⟦R⟧) 
    (≈-refl J)

