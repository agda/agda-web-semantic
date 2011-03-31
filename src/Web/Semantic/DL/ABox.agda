open import Data.Product using ( ∃ ; _×_ ; _,_ )
open import Relation.Unary using ( ∅ ; _∪_ )
open import Web.Semantic.DL.Signature using ( Signature ; CN ; RN )
open import Web.Semantic.Util using ( Subset ; ⁅_⁆ )

module Web.Semantic.DL.ABox where

infixr 5 _∼_ _∈₁_ _∈₂_
infixr 4 _,_

data ABox (Σ : Signature) (X : Set) : Set where
  ε : ABox Σ X
  _,_ : (A B : ABox Σ X) → ABox Σ X
  _∼_ : (x y : X) → ABox Σ X
  _∈₁_ : (x : X) → (c : CN Σ) → ABox Σ X
  _∈₂_ : (xy : X × X) → (r : RN Σ) → ABox Σ X

⟨ABox⟩ : ∀ {Σ X Y} → (X → Y) → ABox Σ X → ABox Σ Y
⟨ABox⟩ f ε              = ε
⟨ABox⟩ f (A , B)        = (⟨ABox⟩ f A , ⟨ABox⟩ f B)
⟨ABox⟩ f (x ∼ y)        = (f x ∼ f y)
⟨ABox⟩ f (x ∈₁ C)       = (f x ∈₁ C)
⟨ABox⟩ f ((x , y) ∈₂ R) = ((f x , f y) ∈₂ R)

Assertions : ∀ {Σ X} → ABox Σ X → Subset (ABox Σ X)
Assertions ε         = ∅
Assertions (A , B)   = (Assertions A) ∪ (Assertions B)
Assertions (x ∼ y)   = ⁅ x ∼ y ⁆
Assertions (x ∈₁ c)  = ⁅ x ∈₁ c ⁆
Assertions (xy ∈₂ r) = ⁅ xy ∈₂ r ⁆
