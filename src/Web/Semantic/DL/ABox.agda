open import Data.Product using ( ∃ ; _×_ )
open import Relation.Unary using ( ∅ ; _∪_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( Concept ; Role )
open import Web.Semantic.Util using ( Subset ; ⁅_⁆ )

module Web.Semantic.DL.ABox where

infixr 5 _∼_ _∈₁_ _∈₂_
infixr 4 _,_

data ABox (Σ : Signature) (X : Set) : Set where
  ε : ABox Σ X
  _,_ : (A B : ABox Σ X) → ABox Σ X
  _∼_ : (x y : X) → ABox Σ X
  _∈₁_ : (x : X) → (C : Concept Σ) → ABox Σ X
  _∈₂_ : (xy : X × X) → (R : Role Σ) → ABox Σ X

Assertions : ∀ {Σ X} → ABox Σ X → Subset (ABox Σ X)
Assertions ε         = ∅
Assertions (A , B)   = (Assertions A) ∪ (Assertions B)
Assertions (x ∼ y)   = ⁅ x ∼ y ⁆
Assertions (x ∈₁ C)  = ⁅ x ∈₁ C ⁆
Assertions (xy ∈₂ R) = ⁅ xy ∈₂ R ⁆
