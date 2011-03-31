open import Data.Product using ( _×_ ; _,_ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.FOL using  ( Formula ; _∈₂_ ; _∈₂_⇒_ )
open import Web.Semantic.DL.FOL.Model using ( _⊨f_ )
open import Web.Semantic.DL.Role using ( Role ; ⟨_⟩ ; ⟨_⟩⁻¹ )
open import Web.Semantic.DL.Role.Model using ( _⟦_⟧₂ ; ⟦⟧₂-resp-≈ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox.Interp using ( Interp ; ≈-sym )

module Web.Semantic.DL.Role.Skolemization {Σ : Signature} where

rskolem : ∀ {Δ} → Role Σ → Δ → Δ → Formula Σ Δ
rskolem ⟨ r ⟩   x y = (x , y) ∈₂ r
rskolem ⟨ r ⟩⁻¹ x y = (y , x) ∈₂ r

rskolem⇒ : ∀ {Δ} → Role Σ → Δ → Δ → Formula Σ Δ → Formula Σ Δ
rskolem⇒ ⟨ r ⟩   x y F = (x , y) ∈₂ r ⇒ F
rskolem⇒ ⟨ r ⟩⁻¹ x y F = (y , x) ∈₂ r ⇒ F

rskolem-sound : ∀ I R x y → (I ⊨f rskolem R x y) → ((x , y) ∈ I ⟦ R ⟧₂)
rskolem-sound I ⟨ r ⟩   x y xy∈⟦r⟧ = xy∈⟦r⟧
rskolem-sound I ⟨ r ⟩⁻¹ x y yx∈⟦r⟧ = yx∈⟦r⟧

rskolem⇒-sound : ∀ I R x y F → (I ⊨f rskolem⇒ R x y F) → ((x , y) ∈ I ⟦ R ⟧₂) → (I ⊨f F)
rskolem⇒-sound I ⟨ r ⟩   x y F xy∈r⇒F xy∈⟦r⟧ = xy∈r⇒F xy∈⟦r⟧
rskolem⇒-sound I ⟨ r ⟩⁻¹ x y F yx∈r⇒F yx∈⟦r⟧ = yx∈r⇒F yx∈⟦r⟧
