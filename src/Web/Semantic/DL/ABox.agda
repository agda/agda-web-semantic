open import Data.Product using ( _×_ )
open import Relation.Unary using ( ∅ ; _∪_ )
open import Web.Semantic.DL.Signature using ( Signature ; IN )
open import Web.Semantic.DL.TBox using ( Concept ; Role )
open import Web.Semantic.Util using ( Subset ; ⁅_⁆ )

module Web.Semantic.DL.ABox where

infixr 5 _∼_ _∈₁_ _∈₂_
infixr 4 _,_

data ABox (Σ : Signature) : Set where
  ε : ABox Σ
  _,_ : (A B : ABox Σ) → ABox Σ
  _∼_ : (i j : IN Σ) → ABox Σ
  _∈₁_ : (i : IN Σ) → (C : Concept Σ) → ABox Σ
  _∈₂_ : (ij : IN Σ × IN Σ) → (R : Role Σ) → ABox Σ

Assertions : ∀ {Σ} → ABox Σ → Subset (ABox Σ)
Assertions ε         = ∅
Assertions (A , B)   = (Assertions A) ∪ (Assertions B)
Assertions (i ∼ j)   = ⁅ i ∼ j ⁆
Assertions (i ∈₁ C)  = ⁅ i ∈₁ C ⁆
Assertions (ij ∈₂ R) = ⁅ ij ∈₂ R ⁆
