open import Data.Product using ( _×_ ; _,_ )
open import Relation.Nullary using ( ¬_ )
open import Relation.Unary using ( _∈_ ; ∅ ; _∪_ )
open import Web.Semantic.DL.ABox using ( ABox ; Assertions ; ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using
  ( Concept ; Role ; TBox ; Axioms
  ; ⟨_⟩ ; ⟨_⟩⁻¹ ; ⊤ ; ⊥ ; _⊓_ ; _⊔_ ; _⇒_ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1
  ; ε ; _,_ ;_⊑₁_ ; _⊑₂_ )
open import Web.Semantic.Util using ( Subset ; ⁅_⁆ )

module Web.Semantic.DL.Judgement {Σ : Signature} {X : Set} where

infixr 2 _▷_⊢_

data _▷_⊢_ (T : TBox Σ) (A : ABox Σ X) : ABox Σ X → Set where
  abox : ∀ {B} → (B ∈ Assertions A) → (T ▷ A ⊢ B)
  ∼-refl : ∀ {x} → (T ▷ A ⊢ x ∼ x)
  ∼-sym : ∀ {x y} → (T ▷ A ⊢ x ∼ y) → (T ▷ A ⊢ y ∼ x)
  ∼-trans : ∀ {x y z} → (T ▷ A ⊢ x ∼ y) → (T ▷ A ⊢ y ∼ z) → (T ▷ A ⊢ x ∼ z)
  ∼-≤1 : ∀ {x y z R} → (T ▷ A ⊢ x ∈₁ (≤1 R)) → (T ▷ A ⊢ (x , y) ∈₂ R) → (T ▷ A ⊢ (x , z) ∈₂ R) → (T ▷ A ⊢ y ∼ z)
  ∈₁-resp-∼ : ∀ {x y C} → (T ▷ A ⊢ x ∈₁ C) → (T ▷ A ⊢ x ∼ y) → (T ▷ A ⊢ y ∈₁ C)
  ∈₁-subsum : ∀ {x C D} → (T ▷ A ⊢ x ∈₁ C) → ((C ⊑₁ D) ∈ Axioms T) → (T ▷ A ⊢ x ∈₁ D)
  ∈₁-⊤-I : ∀ {x} → (T ▷ A ⊢ x ∈₁ ⊤)
  ∈₁-⊓-I : ∀ {x C D} → (T ▷ A ⊢ x ∈₁ C) → (T ▷ A ⊢ x ∈₁ D) → (T ▷ A ⊢ x ∈₁ (C ⊓ D))
  ∈₁-⊓-E₁ : ∀ {x C D} → (T ▷ A ⊢ x ∈₁ (C ⊓ D)) → (T ▷ A ⊢ x ∈₁ C)
  ∈₁-⊓-E₂ : ∀ {x C D} → (T ▷ A ⊢ x ∈₁ (C ⊓ D)) → (T ▷ A ⊢ x ∈₁ D)
  ∈₁-⊔-I₁ : ∀ {x C D} → (T ▷ A ⊢ x ∈₁ C) → (T ▷ A ⊢ x ∈₁ (C ⊔ D))
  ∈₁-⊔-I₂ : ∀ {x C D} → (T ▷ A ⊢ x ∈₁ D) → (T ▷ A ⊢ x ∈₁ (C ⊔ D))
  ∈₁-⇒-E : ∀ {x C D} → (T ▷ A ⊢ x ∈₁ (C ⇒ D)) → (T ▷ A ⊢ x ∈₁ C) → (T ▷ A ⊢ x ∈₁ D)
  ∈₁-∀-E : ∀ {x y R C} → (T ▷ A ⊢ x ∈₁ (∀[ R ] C)) → (T ▷ A ⊢ (x , y) ∈₂ R) → (T ▷ A ⊢ y ∈₁ C)
  ∈₁-∃-I : ∀ {x y R C} → (T ▷ A ⊢ (x , y) ∈₂ R) → (T ▷ A ⊢ y ∈₁ C)  → (T ▷ A ⊢ x ∈₁ (∃⟨ R ⟩ C))
  ∈₂-resp-∼ : ∀ {w x y z R} → (T ▷ A ⊢ w ∼ x) → (T ▷ A ⊢ (x , y) ∈₂ R) → (T ▷ A ⊢ y ∼ z) → (T ▷ A ⊢ (w , z) ∈₂ R)
  ∈₂-subsum : ∀ {xy R S} → (T ▷ A ⊢ xy ∈₂ R) → ((R ⊑₂ S) ∈ Axioms T) → (T ▷ A ⊢ xy ∈₂ S)
  ∈₂-inv-I : ∀ {x y r} → (T ▷ A ⊢ (x , y) ∈₂ ⟨ r ⟩) → (T ▷ A ⊢ (y , x) ∈₂ ⟨ r ⟩⁻¹)
  ∈₂-inv-E : ∀ {x y r} → (T ▷ A ⊢ (x , y) ∈₂ ⟨ r ⟩⁻¹) → (T ▷ A ⊢ (y , x) ∈₂ ⟨ r ⟩)
