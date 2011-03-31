open import Data.Product using ( _×_ ; _,_ )
open import Data.Sum using ( _⊎_ )
open import Relation.Unary using ( _∈_ ; _∉_ )
open import Web.Semantic.DL.FOL using  ( Formula ; true ; false ; _∧_ ; _∈₁_ ; _∈₁_⇒_ ; _∈₂_ ; _∈₂_⇒_ ; _∼_ ; _∼_⇒_ ; ∀₁ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox.Interp using ( Interp ; Δ ; _⊨_≈_ ; con ; rol )
open import Web.Semantic.Util using ( True ; False )

module Web.Semantic.DL.FOL.Model {Σ : Signature} where

_⊨f_ : (I : Interp Σ) → Formula Σ (Δ I) → Set
I ⊨f true = True
I ⊨f false = False
I ⊨f (F ∧ G) = (I ⊨f F) × (I ⊨f G)
I ⊨f (x ∈₁ c) = x ∈ (con I c)
I ⊨f (x ∈₁ c ⇒ F) = (x ∈ (con I c)) → (I ⊨f F)
I ⊨f ((x , y) ∈₂ r) = (x , y) ∈ (rol I r)
I ⊨f ((x , y) ∈₂ r ⇒ F) = ((x , y) ∈ (rol I r)) → (I ⊨f F)
I ⊨f (x ∼ y) = I ⊨ x ≈ y
I ⊨f (x ∼ y ⇒ F) = (I ⊨ x ≈ y) → (I ⊨f F)
I ⊨f ∀₁ F = ∀ x → (I ⊨f F x)
