open import Data.Product using ( _×_ ; _,_ )
open import Web.Semantic.DL.ABox.Model using ( _⊨a_ ; ⊨a-resp-≲ )
open import Web.Semantic.DL.ABox.Interp using ( Interp ; ⌊_⌋ )
open import Web.Semantic.DL.ABox.Interp.Morphism using ( _≃_ ; ≃⌊_⌋ ; ≃-impl-≲ )
open import Web.Semantic.DL.KB using ( KB ; tbox ; abox )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox.Model using ( _⊨t_ ; ⊨t-resp-≃ )

module Web.Semantic.DL.KB.Model {Σ : Signature} {X : Set} where

infixr 2 _⊨_

_⊨_ : Interp Σ X → KB Σ X → Set
I ⊨ K = (⌊ I ⌋ ⊨t tbox K) × (I ⊨a abox K)

⊨-resp-≃ : ∀ {I J} → (I ≃ J) → ∀ K → (I ⊨ K) → (J ⊨ K)
⊨-resp-≃ I≃J K (I⊨T , I⊨A) =
  (⊨t-resp-≃ ≃⌊ I≃J ⌋ (tbox K) I⊨T , ⊨a-resp-≲ (≃-impl-≲ I≃J) (abox K) I⊨A)
