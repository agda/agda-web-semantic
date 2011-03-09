open import Data.Product using ( _×_ ; _,_ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.Interp using ( Interp ; rol ; _⊨_≈_ ; rol-≈ ; ≈-sym )
open import Web.Semantic.DL.Interp.Order using ( _≤_ ; ≤-resp-rol )
open import Web.Semantic.DL.Role using ( Role ; ⟨_⟩ ; ⟨_⟩⁻¹ )
open import Web.Semantic.DL.ABox.Signature using ( Signature ; tsig )
open import Web.Semantic.Util using ( Subset ; _⁻¹ )

module Web.Semantic.DL.Role.Model {Σ : Signature} {Δ : Set} where

_⟦_⟧₂ : ∀ (I : Interp Σ Δ) → Role (tsig Σ) → Subset (Δ × Δ)
I ⟦ ⟨ r ⟩   ⟧₂ = rol I r
I ⟦ ⟨ r ⟩⁻¹ ⟧₂ = (rol I r)⁻¹

⟦⟧₂-resp-≈ : ∀ I R {w x y z} → 
  (I ⊨ w ≈ x) → ((x , y) ∈ I ⟦ R ⟧₂) → (I ⊨ y ≈ z) → ((w , z) ∈ I ⟦ R ⟧₂) 
⟦⟧₂-resp-≈ I ⟨ r ⟩   w≈x xy∈⟦r⟧ y≈z = rol-≈ I r w≈x xy∈⟦r⟧ y≈z
⟦⟧₂-resp-≈ I ⟨ r ⟩⁻¹ w≈x yx∈⟦r⟧ y≈z = rol-≈ I r (≈-sym I y≈z) yx∈⟦r⟧ (≈-sym I w≈x)

⟦⟧₂-resp-≤ : ∀ {I J : Interp Σ Δ} → (I≤J : I ≤ J) → ∀ {xy} R → (xy ∈ I ⟦ R ⟧₂) → (xy ∈ J ⟦ R ⟧₂)
⟦⟧₂-resp-≤ I≤J {x , y} ⟨ r ⟩   xy∈⟦r⟧ = ≤-resp-rol I≤J xy∈⟦r⟧
⟦⟧₂-resp-≤ I≤J {x , y} ⟨ r ⟩⁻¹ yx∈⟦r⟧ = ≤-resp-rol I≤J yx∈⟦r⟧
