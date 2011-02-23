open import Data.Product using ( _×_ ; _,_ )
open import Relation.Nullary using ( ¬_ )
open import Relation.Unary using ( _∈_ ; ∅ ; _∪_ )
open import Web.Semantic.DL.ABox using 
  ( ABox ; Assertions ; ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.KB using ( KB ; tbox ; abox )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using
  ( Concept ; Role ; TBox ; Axioms
  ; ⟨_⟩ ; ⟨_⟩⁻¹ ; ⊤ ; ⊥ ; _⊓_ ; _⊔_ ; ¬ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1
  ; ε ; _,_ ;_⊑₁_ ; _⊑₂_ )
open import Web.Semantic.Util using ( Subset ; ⁅_⁆ )

module Web.Semantic.DL.Sequent {Σ : Signature} {X : Set} where

infixr 2 _⊢_

data _⊢_ (K : KB Σ X) : ABox Σ X → Set where
  assert : ∀ {B} → (B ∈ Assertions (abox K)) → (K ⊢ B)
  ∼-refl : ∀ {x} → (K ⊢ x ∼ x)
  ∼-sym : ∀ {x y} → (K ⊢ x ∼ y) → (K ⊢ y ∼ x)
  ∼-trans : ∀ {x y z} → (K ⊢ x ∼ y) → (K ⊢ y ∼ z) → (K ⊢ x ∼ z)
  ∼-≤1 : ∀ {x y z R} → (K ⊢ x ∈₁ (≤1 R)) → (K ⊢ (x , y) ∈₂ R) → (K ⊢ (x , z) ∈₂ R) → (K ⊢ y ∼ z)
  ∈₁-resp-∼ : ∀ {x y C} → (K ⊢ x ∈₁ C) → (K ⊢ x ∼ y) → (K ⊢ y ∈₁ C)
  ∈₁-subsum : ∀ {x C D} → (K ⊢ x ∈₁ C) → ((C ⊑₁ D) ∈ Axioms (tbox K)) → (K ⊢ x ∈₁ D)
  ∈₁-⊤-I : ∀ {x} → (K ⊢ x ∈₁ ⊤)
  ∈₁-⊓-I : ∀ {x C D} → (K ⊢ x ∈₁ C) → (K ⊢ x ∈₁ D) → (K ⊢ x ∈₁ (C ⊓ D))
  ∈₁-⊓-E₁ : ∀ {x C D} → (K ⊢ x ∈₁ (C ⊓ D)) → (K ⊢ x ∈₁ C)
  ∈₁-⊓-E₂ : ∀ {x C D} → (K ⊢ x ∈₁ (C ⊓ D)) → (K ⊢ x ∈₁ D)
  ∈₁-⊔-I₁ : ∀ {x C D} → (K ⊢ x ∈₁ C) → (K ⊢ x ∈₁ (C ⊔ D))
  ∈₁-⊔-I₂ : ∀ {x C D} → (K ⊢ x ∈₁ D) → (K ⊢ x ∈₁ (C ⊔ D))
  ∈₁-∀-E : ∀ {x y R C} → (K ⊢ x ∈₁ (∀[ R ] C)) → (K ⊢ (x , y) ∈₂ R) → (K ⊢ y ∈₁ C)
  ∈₁-∃-I : ∀ {x y R C} → (K ⊢ (x , y) ∈₂ R) → (K ⊢ y ∈₁ C)  → (K ⊢ x ∈₁ (∃⟨ R ⟩ C))
  ∈₂-resp-∼ : ∀ {w x y z R} → (K ⊢ w ∼ x) → (K ⊢ (x , y) ∈₂ R) → (K ⊢ y ∼ z) → (K ⊢ (w , z) ∈₂ R)
  ∈₂-subsum : ∀ {xy R S} → (K ⊢ xy ∈₂ R) → ((R ⊑₂ S) ∈ Axioms (tbox K)) → (K ⊢ xy ∈₂ S)
  ∈₂-inv-I : ∀ {x y r} → (K ⊢ (x , y) ∈₂ ⟨ r ⟩) → (K ⊢ (y , x) ∈₂ ⟨ r ⟩⁻¹)
  ∈₂-inv-E : ∀ {x y r} → (K ⊢ (x , y) ∈₂ ⟨ r ⟩⁻¹) → (K ⊢ (y , x) ∈₂ ⟨ r ⟩)
