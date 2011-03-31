open import Data.Product using ( _×_ )
open import Web.Semantic.DL.Signature using ( Signature ; CN ; RN )

module Web.Semantic.DL.FOL where

-- A fragment of first order logic with no existentials or disjunctions.

infixr 4 _∧_

data Formula (Σ : Signature) (Δ : Set) : Set where
  true : Formula Σ Δ
  false : Formula Σ Δ
  _∧_ : Formula Σ Δ → Formula Σ Δ → Formula Σ Δ
  _∈₁_ : Δ → CN Σ → Formula Σ Δ
  _∈₁_⇒_ : Δ → CN Σ → Formula Σ Δ → Formula Σ Δ
  _∈₂_ : (Δ × Δ) → RN Σ → Formula Σ Δ
  _∈₂_⇒_ : (Δ × Δ) → RN Σ → Formula Σ Δ → Formula Σ Δ
  _∼_ : Δ → Δ → Formula Σ Δ
  _∼_⇒_ : Δ → Δ → Formula Σ Δ → Formula Σ Δ
  ∀₁ : (Δ → Formula Σ Δ) → Formula Σ Δ
