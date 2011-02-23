open import Data.Product using ( ∃ ; _×_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ )
open import Web.Semantic.DL.ABox.Model using ( _⊨a_ )
open import Web.Semantic.DL.Interp using ( Interp ; ⟨Interp⟩ )
open import Web.Semantic.DL.KB using ( KB ; tbox ; abox )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox.Model using ( _⊨t_ )

module Web.Semantic.DL.KB.Model {Σ : Signature} {X : Set} where

infixr 2 _⊨_

_⊨_ : Interp Σ X → KB Σ X → Set
I ⊨ K = (I ⊨t tbox K) × (I ⊨a abox K)
