open import Web.Semantic.DL.Role using ( Role )
open import Web.Semantic.DL.TBox.Signature using ( Signature ; CN ; RN )

module Web.Semantic.DL.Concept where

infixr 9 ∀[_]_
infixr 8 ∃⟨_⟩_
infixl 7 _⊓_
infixl 6 _⊔_ 

data Concept (Σ : Signature) : Set where
  ⟨_⟩ : (c : CN Σ) → Concept Σ
  ¬⟨_⟩ : (c : CN Σ) → Concept Σ
  ⊤ : Concept Σ
  ⊥ : Concept Σ
  _⊓_ : (C D : Concept Σ) → Concept Σ
  _⊔_ : (C D : Concept Σ) → Concept Σ
  ∀[_]_ : (R : Role Σ) (C : Concept Σ) → Concept Σ
  ∃⟨_⟩_ : (R : Role Σ) (C : Concept Σ) → Concept Σ
  ≤1 : (R : Role Σ) → Concept Σ
  >1 : (R : Role Σ) → Concept Σ

neg : ∀ {Σ} (C : Concept Σ) → Concept Σ
neg ⟨ c ⟩      = ¬⟨ c ⟩
neg ¬⟨ c ⟩     = ⟨ c ⟩
neg ⊤          = ⊥
neg ⊥          = ⊤
neg (C ⊓ D)    = neg C ⊔ neg D
neg (C ⊔ D)    = neg C ⊓ neg D
neg (∀[ R ] C) = ∃⟨ R ⟩ neg C
neg (∃⟨ R ⟩ C) = ∀[ R ] neg C
neg (≤1 R)     = >1 R
neg (>1 R)     = ≤1 R
