open import Data.Product using ( _×_ ; _,_ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox.Signature using ( Signature ; IN ; tsig )
open import Web.Semantic.DL.FOL using  ( Formula ; _∈₂_ ; _∈₂_⇒_ )
open import Web.Semantic.DL.FOL.Model using ( _⊨f_ )
open import Web.Semantic.DL.Interp using ( Interp ; Quotient ; ≈-sym )
open import Web.Semantic.DL.Role using ( Role ; ⟨_⟩ ; ⟨_⟩⁻¹ )
open import Web.Semantic.DL.Role.Model using ( _⟦_⟧₂ ; ⟦⟧₂-resp-≈ )

module Web.Semantic.DL.Role.Skolemization {Σ : Signature} where

rskolem : Role (tsig Σ) → IN Σ → IN Σ → Formula Σ
rskolem ⟨ r ⟩ x y = (x , y) ∈₂ r
rskolem ⟨ r ⟩⁻¹ x y = (y , x) ∈₂ r

rskolem⇒ : Role (tsig Σ) → IN Σ → IN Σ → Formula Σ → Formula Σ
rskolem⇒ ⟨ r ⟩   x y F = (x , y) ∈₂ r ⇒ F
rskolem⇒ ⟨ r ⟩⁻¹ x y F = (y , x) ∈₂ r ⇒ F

rskolem-sound : ∀ I R x y → (I ∈ Quotient Σ) → (I ⊨f rskolem R x y) → ((x , y) ∈ I ⟦ R ⟧₂)
rskolem-sound I ⟨ r ⟩   x y I✓ xy∈⟦r⟧ = ⟦⟧₂-resp-≈ I ⟨ r ⟩ I✓ xy∈⟦r⟧ (≈-sym I I✓)
rskolem-sound I ⟨ r ⟩⁻¹ x y I✓ yx∈⟦r⟧ = ⟦⟧₂-resp-≈ I ⟨ r ⟩ I✓ yx∈⟦r⟧ (≈-sym I I✓)

rskolem⇒-sound : ∀ I R x y F → (I ∈ Quotient Σ) → (I ⊨f rskolem⇒ R x y F) → ((x , y) ∈ I ⟦ R ⟧₂) → (I ⊨f F)
rskolem⇒-sound I ⟨ r ⟩   x y F I✓ xy∈r⇒F xy∈⟦r⟧ = xy∈r⇒F (⟦⟧₂-resp-≈ I ⟨ r ⟩ (≈-sym I I✓) xy∈⟦r⟧ I✓)
rskolem⇒-sound I ⟨ r ⟩⁻¹ x y F I✓ yx∈r⇒F yx∈⟦r⟧ = yx∈r⇒F (⟦⟧₂-resp-≈ I ⟨ r ⟩ (≈-sym I I✓) yx∈⟦r⟧ I✓)
