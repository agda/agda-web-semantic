open import Data.Product using ( ∃ ; _×_ )
open import Relation.Unary using ( ∅ ; _∪_ )
open import Web.Semantic.DL.ABox.Signature using ( Signature ; IN ; tsig )
open import Web.Semantic.DL.Concept using ( Concept )
open import Web.Semantic.DL.Role using ( Role )
open import Web.Semantic.Util using ( Subset ; ⁅_⁆ )

module Web.Semantic.DL.ABox where

infixr 5 _∼_ _∈₁_ _∈₂_
infixr 4 _,_

data ABox (Σ : Signature) : Set where
  ε : ABox Σ
  _,_ : (A B : ABox Σ) → ABox Σ
  _∼_ : (x y : IN Σ) → ABox Σ
  _∈₁_ : (x : IN Σ) → (C : Concept (tsig Σ)) → ABox Σ
  _∈₂_ : (xy : IN Σ × IN Σ) → (R : Role (tsig Σ)) → ABox Σ

Assertions : ∀ {Σ} → ABox Σ → Subset (ABox Σ)
Assertions ε         = ∅
Assertions (A , B)   = (Assertions A) ∪ (Assertions B)
Assertions (x ∼ y)   = ⁅ x ∼ y ⁆
Assertions (x ∈₁ C)  = ⁅ x ∈₁ C ⁆
Assertions (xy ∈₂ R) = ⁅ xy ∈₂ R ⁆
