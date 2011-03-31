open import Data.Product using ( ∃ ; _×_ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox.Interp using ( Interp ; _*_ )
open import Web.Semantic.DL.ABox.Interp.Morphism using ( _≲_ ; ≲-trans ; _**_ ; _≋_ )
open import Web.Semantic.DL.KB using ( KB )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.Util using ( _⊕_⊕_ ; inode ; enode )

module Web.Semantic.DL.KB.Initial {Σ : Signature} {X V Y : Set} where

infix 5 _>>_ 
infix 2 _⊕_⊨_

-- J ∈ Initial I K whenever J is the initial extension of I
-- satisfying K, that is there is I≲J s.t. I ⊨ K
-- and for any other such I≲K, there is a unique
-- J≲K which commutes with I≲J and I≲K.

_>>_ : ∀ {I : Interp Σ X} {J K : Interp Σ (X ⊕ V ⊕ Y)} →
  (I ≲ inode * J) → (J ≲ K) → (I ≲ inode * K)
I≲J >> J≲K = ≲-trans I≲J (inode ** J≲K)

Unique : ∀ (I : Interp Σ X) → (J K : Interp Σ (X ⊕ V ⊕ Y)) →
  (I ≲ inode * J) → (I ≲ inode * K) → (J ≲ K) → Set₁
Unique I J K I≲J I≲K J≲K =
  ∀ J≲K′ → (I≲K ≋ I≲J >> J≲K′) → (J≲K ≋ J≲K′)

data Mediated (I : Interp Σ X) (J K : Interp Σ (X ⊕ V ⊕ Y))
  (I≲J : I ≲ inode * J) (I≲K : I ≲ inode * K) : Set₁ where
    _,_ : (J≲K : J ≲ K) → (I≲K ≋ I≲J >> J≲K) × (Unique I J K I≲J I≲K J≲K)
      → Mediated I J K I≲J I≲K

Mediator : ∀ (I : Interp Σ X) → (J : Interp Σ (X ⊕ V ⊕ Y)) →
  (I ≲ inode * J) → (KB Σ (X ⊕ V ⊕ Y)) → Set₁
Mediator I J I≲J KB = 
  ∀ K (I≲K : I ≲ inode * K) → (K ⊨ KB) → Mediated I J K I≲J I≲K

data Initial I KB (J : Interp Σ (X ⊕ V ⊕ Y)) : Set₁ where
  _,_ : ∀ (I≲J : I ≲ inode * J) → (J ⊨ KB) × (Mediator I J I≲J KB) → 
    (J ∈ Initial I KB)

-- I ⊕ KB₁ ⊨ KB₂ whenever the initial extension of I satisfying
-- KB₁ exists, and has exports satisfying KB₂.

data _⊕_⊨_ I (KB₁ : KB Σ (X ⊕ V ⊕ Y)) KB₂ : Set₁ where
    _,_ : ∀ J → ((J ∈ Initial I KB₁) × (enode * J ⊨ KB₂)) → (I ⊕ KB₁ ⊨ KB₂)

