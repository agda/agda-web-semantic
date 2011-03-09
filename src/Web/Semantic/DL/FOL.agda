open import Data.Product using ( _×_ )
open import Web.Semantic.DL.ABox.Signature using ( Signature ; IN ; CN ; RN )

module Web.Semantic.DL.FOL where

-- A fragment of first order logic with only universal quantifiers.

infixr 4 _∧_  _∨_ _⇒_

data Formula (Σ : Signature) : Set where
  true : Formula Σ
  false : Formula Σ
  _∧_ : Formula Σ → Formula Σ → Formula Σ
  _∨_ : Formula Σ → Formula Σ → Formula Σ
  _⇒_ : Formula Σ → Formula Σ → Formula Σ
  _∈₁_ : IN Σ → CN Σ → Formula Σ
  _∈₂_ : (IN Σ × IN Σ) → RN Σ → Formula Σ
  _∼_ : IN Σ → IN Σ → Formula Σ
  ∀₁ : (IN Σ → Formula Σ) → Formula Σ
