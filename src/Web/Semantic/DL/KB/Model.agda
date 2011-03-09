open import Data.Product using ( _×_ ; _,_ )
open import Web.Semantic.DL.ABox.Model using ( _⊨a_ ; ⊨a-resp-≤≥ )
open import Web.Semantic.DL.ABox.Signature using ( Signature )
open import Web.Semantic.DL.Interp using ( Interp )
open import Web.Semantic.DL.Interp.Order using ( _≤_ )
open import Web.Semantic.DL.KB using ( KB ; tbox ; abox )
open import Web.Semantic.DL.TBox.Model using ( _⊨t_ ; ⊨t-resp-≤≥ )

module Web.Semantic.DL.KB.Model {Σ : Signature} {Δ : Set} where

infixr 2 _⊨_

_⊨_ : Interp Σ Δ → KB Σ → Set
I ⊨ K = (I ⊨t tbox K) × (I ⊨a abox K)

⊨-resp-≤≥ : ∀ {I J : Interp Σ Δ} → (I ≤ J) → (J ≤ I) → ∀ K → (I ⊨ K) → (J ⊨ K)
⊨-resp-≤≥ I≤J J≤I K (I⊨T , I⊨A) = (⊨t-resp-≤≥ I≤J J≤I (tbox K) I⊨T , ⊨a-resp-≤≥ I≤J J≤I (abox K) I⊨A)
