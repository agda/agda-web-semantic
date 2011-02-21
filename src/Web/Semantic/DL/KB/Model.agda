open import Data.Product using ( ∃ ; _×_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ )
open import Web.Semantic.DL.ABox.Model using ( _⊨a_ )
open import Web.Semantic.DL.Interp using ( Interp ; ⟨Interp⟩ )
open import Web.Semantic.DL.KB using ( KB ; _⊕_ ; named ; tbox ; abox )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox.Model using ( _⊨t_ )

module Web.Semantic.DL.KB.Model {Σ : Signature} {X : Set} where

infixr 2 _⊨_

pack : ∀ {W} → Interp Σ (W ⊕ X) → Interp Σ X
pack = ⟨Interp⟩ named

_⊨_ : Interp Σ X → KB Σ X → Set₁
I ⊨ K = ∃ λ J → (I ≡ pack J) × (J ⊨t tbox K) × (J ⊨a abox K)
