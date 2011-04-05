open import Data.Product using ( ∃ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox )
open import Web.Semantic.DL.ABox.Interp using ( Interp ; _*_ )
open import Web.Semantic.DL.ABox.Interp.Morphism using ( _≲_ ; ≲-trans ; _**_ ; _≋_ )
open import Web.Semantic.DL.KB using ( KB ; _,_ ; tbox )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( _,_ )
open import Web.Semantic.Util using ( _⊕_⊕_ ; inode ; enode )

module Web.Semantic.DL.Integrity {Σ : Signature} {X V Y : Set} where

-- A variant of the notion of OWL integrity in:

--   Boris Motik, Ian Horrocks, and Ulrike Sattler. Bridging the gap between OWL and
--   relational databases. In Proc. Conf. World Wide Web (WWW2007), pp 807–816, 2007.

-- They propose defining that an integrity constraint S (given as a T-Box) is valid
-- for a knowlege base K whenever S is valid in every minimal Herbrand model.
-- We strengthen this requirement to say that there is a minimal model of K,
-- which validtes S.

infixr 4 _>>_ _,_
infix 2 _⊕_⊨_

-- J ∈ Initial I K whenever J is the initial extension of I
-- satisfying K, that is there is I≲J s.t. I ⊨ K
-- and for any other such I≲K, there is a unique
-- J≲K which commutes with I≲J and I≲K.

_>>_ : ∀ {I : Interp Σ X} {J K : Interp Σ (X ⊕ V ⊕ Y)} →
  (I ≲ inode * J) → (J ≲ K) → (I ≲ inode * K)
I≲J >> J≲K = ≲-trans I≲J (inode ** J≲K)

Unique : ∀ (I : Interp Σ X) → (J K : Interp Σ (X ⊕ V ⊕ Y)) →
  (I ≲ inode * J) → (I ≲ inode * K) → Set
Unique I J K I≲J I≲K = ∀ (J≲₁K J≲₂K : J ≲ K) → 
  (I≲K ≋ I≲J >> J≲₁K) → (I≲K ≋ I≲J >> J≲₂K) → (J≲₁K ≋ J≲₂K)

data Mediated (I : Interp Σ X) (J K : Interp Σ (X ⊕ V ⊕ Y))
  (I≲J : I ≲ inode * J) (I≲K : I ≲ inode * K) : Set where
    _,_ : (J≲K : J ≲ K) → (I≲K ≋ I≲J >> J≲K) × (Unique I J K I≲J I≲K)
      → Mediated I J K I≲J I≲K

med-≲ : ∀ {I} {J K : Interp Σ (X ⊕ V ⊕ Y)} {I≲J I≲K} → 
  (Mediated I J K I≲J I≲K) → (J ≲ K)
med-≲ (J≲K , I≲K≋I≲J≲K , J≲K-uniq) = J≲K

med-≋ : ∀ {I} {J K : Interp Σ (X ⊕ V ⊕ Y)} {I≲J I≲K} → 
  (m : Mediated I J K I≲J I≲K) → (I≲K ≋ I≲J >> med-≲ m)
med-≋ (J≲K , I≲K≋I≲J≲K , J≲K-uniq) = I≲K≋I≲J≲K

med-uniq : ∀ {I} {J K : Interp Σ (X ⊕ V ⊕ Y)} {I≲J I≲K} → 
  (Mediated I J K I≲J I≲K) → Unique I J K I≲J I≲K
med-uniq (J≲K , I≲K≋I≲J≲K , J≲K-uniq) = J≲K-uniq

Mediator : ∀ (I : Interp Σ X) → (J : Interp Σ (X ⊕ V ⊕ Y)) →
  (I ≲ inode * J) → (KB Σ (X ⊕ V ⊕ Y)) → Set₁
Mediator I J I≲J KB = 
  ∀ K (I≲K : I ≲ inode * K) → (K ⊨ KB) → Mediated I J K I≲J I≲K

data Initial I KB (J : Interp Σ (X ⊕ V ⊕ Y)) : Set₁ where
  _,_ : ∀ (I≲J : I ≲ inode * J) → (J ⊨ KB) × (Mediator I J I≲J KB) → 
    (J ∈ Initial I KB)

init-≲ : ∀ {I KB} {J : Interp Σ (X ⊕ V ⊕ Y)} → 
  (J ∈ Initial I KB) → (I ≲ inode * J)
init-≲ (I≲J , J⊨KB , J-med) = I≲J

init-⊨ : ∀ {I KB} {J : Interp Σ (X ⊕ V ⊕ Y)} → 
  (J ∈ Initial I KB) → (J ⊨ KB)
init-⊨ (I≲J , J⊨KB , J-med) = J⊨KB

init-med : ∀ {I KB} {J : Interp Σ (X ⊕ V ⊕ Y)} → 
  (J-init : J ∈ Initial I KB) → Mediator I J (init-≲ J-init) KB
init-med (I≲J , J⊨KB , J-med) = J-med

-- I ⊕ KB₁ ⊨ KB₂ whenever the initial extension of I satisfying
-- KB₁ exists, and has exports satisfying KB₂.

data _⊕_⊨_ I (KB₁ : KB Σ (X ⊕ V ⊕ Y)) KB₂ : Set₁ where
    _,_ : ∀ J → ((J ∈ Initial I KB₁) × (enode * J ⊨ KB₂)) → (I ⊕ KB₁ ⊨ KB₂)

extension : ∀ {I KB₁ KB₂} → (I ⊕ KB₁ ⊨ KB₂) → (Interp Σ (X ⊕ V ⊕ Y))
extension (J , J-init , J⊨KB₂) = J

ext-init : ∀ {I} {KB₁ : KB Σ (X ⊕ V ⊕ Y)} {KB₂} → 
  (I⊕KB₁⊨KB₂ : I ⊕ KB₁ ⊨ KB₂) → (extension I⊕KB₁⊨KB₂ ∈ Initial I KB₁)
ext-init (J , J-init , J⊨KB₂) = J-init

ext-⊨ : ∀ {I} {KB₁ : KB Σ (X ⊕ V ⊕ Y)} {KB₂} → 
  (I⊕KB₁⊨KB₂ : I ⊕ KB₁ ⊨ KB₂) → (enode * (extension I⊕KB₁⊨KB₂) ⊨ KB₂)
ext-⊨ (J , J-init , J⊨KB₂) = J⊨KB₂

ext✓ : ∀ {I S T} {F : ABox Σ (X ⊕ V ⊕ Y)} {B} →
  (I⊕SF⊨TB : I ⊕ S , F ⊨ T , B) →
    (enode * (extension I⊕SF⊨TB) ⊨ (S , T) , B)
ext✓ I⊕SF⊨TB = 
  ( ( proj₁ (init-⊨ (ext-init I⊕SF⊨TB)) 
    , proj₁ (ext-⊨ I⊕SF⊨TB) ) 
  , proj₂ (ext-⊨ I⊕SF⊨TB) )
