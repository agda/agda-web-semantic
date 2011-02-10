open import Relation.Unary using ( ∅ ; _∪_ )
open import Web.Semantic.DL.Signature using ( Signature ; CN ; RN )
open import Web.Semantic.Util using ( Subset ; ⁅_⁆ )

module Web.Semantic.DL.TBox where

infixr 9 ∀[_]_
infixr 8 ∃⟨_⟩_
infixl 7 _⊓_
infixl 6 _⊔_ 
infixl 5 _⊑₁_ _⊑₂_
infixr 4 _,_

data Role (Σ : Signature) : Set where
  ⟨_⟩ : (r : RN Σ) → Role Σ
  ⟨_⟩⁻¹ : (r : RN Σ) → Role Σ

data Concept (Σ : Signature) : Set where
  ⟨_⟩ : (c : CN Σ) → Concept Σ
  ⊤ : Concept Σ
  ⊥ : Concept Σ
  _⊓_ : (C D : Concept Σ) → Concept Σ
  _⊔_ : (C D : Concept Σ) → Concept Σ
  _⇒_ : (C D : Concept Σ) → Concept Σ
  ∀[_]_ : (R : Role Σ) (C : Concept Σ) → Concept Σ
  ∃⟨_⟩_ : (R : Role Σ) (C : Concept Σ) → Concept Σ
  ≤1 : (R : Role Σ) → Concept Σ

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
