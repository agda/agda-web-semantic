open import Relation.Unary using ( ∅ ; _∪_ )
open import Web.Semantic.DL.Concept using ( Concept )
open import Web.Semantic.DL.Role using ( Role )
open import Web.Semantic.DL.TBox.Signature using ( Signature )
open import Web.Semantic.Util using ( Subset ; ⁅_⁆ )

module Web.Semantic.DL.TBox where

infixl 5 _⊑₁_ _⊑₂_
infixr 4 _,_

data TBox (Σ : Signature) : Set where
  ε : TBox Σ 
  _,_ : (T U : TBox Σ) → TBox Σ
  _⊑₁_ : (C D : Concept Σ) → TBox Σ
  _⊑₂_ : (Q R : Role Σ) → TBox Σ

Axioms : ∀ {Σ} → TBox Σ → Subset (TBox Σ)
Axioms ε        = ∅
Axioms (T , U)  = (Axioms T) ∪ (Axioms U)
Axioms (C ⊑₁ D) = ⁅ C ⊑₁ D ⁆
Axioms (Q ⊑₂ R) = ⁅ Q ⊑₂ R ⁆
