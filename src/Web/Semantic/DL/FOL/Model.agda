open import Data.Product using ( _×_ ; _,_ )
open import Data.Sum using ( _⊎_ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox.Signature using ( Signature )
open import Web.Semantic.DL.FOL using  ( Formula ; true ; false ; _∧_ ; _∨_ ; _⇒_ ; _∈₁_ ; _∈₂_ ; _∼_ ; ∀₁ )
open import Web.Semantic.DL.Interp using ( Interp ; _⊨_≈_ ; ind ; con ; rol )
open import Web.Semantic.Util using ( True ; False )

module Web.Semantic.DL.FOL.Model {Σ : Signature} {Δ : Set} where

_⊨f_ : Interp Σ Δ → Formula Σ → Set
I ⊨f true = True
I ⊨f false = False
I ⊨f (F ∧ G) = (I ⊨f F) × (I ⊨f G)
I ⊨f (F ∨ G) = (I ⊨f F) ⊎ (I ⊨f G)
I ⊨f (F ⇒ G) = (I ⊨f F) → (I ⊨f G)
I ⊨f (x ∈₁ c) = (ind I x) ∈ (con I c)
I ⊨f ((x , y) ∈₂ r) = (ind I x , ind I y) ∈ (rol I r)
I ⊨f (x ∼ y) = I ⊨ (ind I x) ≈ (ind I y)
I ⊨f ∀₁ F = ∀ x → (I ⊨f F x)
