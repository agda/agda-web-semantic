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

module Web.Semantic.DL.Judgement {Σ : Signature} where

infixr 2 _▷_⊢_

data _▷_⊢_ (T : TBox Σ) (A : ABox Σ) : ABox Σ → Set where
  abox : ∀ {B} → (B ∈ Assertions A) → (T ▷ A ⊢ B)
  ∼-refl : ∀ {i} → (T ▷ A ⊢ i ∼ i)
  ∼-sym : ∀ {i j} → (T ▷ A ⊢ i ∼ j) → (T ▷ A ⊢ j ∼ i)
  ∼-trans : ∀ {i j k} → (T ▷ A ⊢ i ∼ j) → (T ▷ A ⊢ j ∼ k) → (T ▷ A ⊢ i ∼ k)
  ∼-≤1 : ∀ {i j k R} → (T ▷ A ⊢ i ∈₁ (≤1 R)) → (T ▷ A ⊢ (i , j) ∈₂ R) → (T ▷ A ⊢ (i , k) ∈₂ R) → (T ▷ A ⊢ j ∼ k)
  ∈₁-resp-∼ : ∀ {i j C} → (T ▷ A ⊢ i ∈₁ C) → (T ▷ A ⊢ i ∼ j) → (T ▷ A ⊢ j ∈₁ C)
  ∈₁-subsum : ∀ {i C D} → (T ▷ A ⊢ i ∈₁ C) → ((C ⊑₁ D) ∈ Axioms T) → (T ▷ A ⊢ i ∈₁ D)
  ∈₁-⊤-I : ∀ {i} → (T ▷ A ⊢ i ∈₁ ⊤)
  ∈₁-⊓-I : ∀ {i C D} → (T ▷ A ⊢ i ∈₁ C) → (T ▷ A ⊢ i ∈₁ D) → (T ▷ A ⊢ i ∈₁ (C ⊓ D))
  ∈₁-⊓-E₁ : ∀ {i C D} → (T ▷ A ⊢ i ∈₁ (C ⊓ D)) → (T ▷ A ⊢ i ∈₁ C)
  ∈₁-⊓-E₂ : ∀ {i C D} → (T ▷ A ⊢ i ∈₁ (C ⊓ D)) → (T ▷ A ⊢ i ∈₁ D)
  ∈₁-⊔-I₁ : ∀ {i C D} → (T ▷ A ⊢ i ∈₁ C) → (T ▷ A ⊢ i ∈₁ (C ⊔ D))
  ∈₁-⊔-I₂ : ∀ {i C D} → (T ▷ A ⊢ i ∈₁ D) → (T ▷ A ⊢ i ∈₁ (C ⊔ D))
  ∈₁-⇒-E : ∀ {i C D} → (T ▷ A ⊢ i ∈₁ (C ⇒ D)) → (T ▷ A ⊢ i ∈₁ C) → (T ▷ A ⊢ i ∈₁ D)
  ∈₁-∀-E : ∀ {i j R C} → (T ▷ A ⊢ i ∈₁ (∀[ R ] C)) → (T ▷ A ⊢ (i , j) ∈₂ R) → (T ▷ A ⊢ j ∈₁ C)
  ∈₁-∃-I : ∀ {i j R C} → (T ▷ A ⊢ (i , j) ∈₂ R) → (T ▷ A ⊢ j ∈₁ C)  → (T ▷ A ⊢ i ∈₁ (∃⟨ R ⟩ C))
  ∈₂-resp-∼ : ∀ {i j k l R} → (T ▷ A ⊢ i ∼ j) → (T ▷ A ⊢ (j , k) ∈₂ R) → (T ▷ A ⊢ k ∼ l) → (T ▷ A ⊢ (i , l) ∈₂ R)
  ∈₂-subsum : ∀ {ij R S} → (T ▷ A ⊢ ij ∈₂ R) → ((R ⊑₂ S) ∈ Axioms T) → (T ▷ A ⊢ ij ∈₂ S)
  ∈₂-inv-I : ∀ {i j r} → (T ▷ A ⊢ (i , j) ∈₂ ⟨ r ⟩) → (T ▷ A ⊢ (j , i) ∈₂ ⟨ r ⟩⁻¹)
  ∈₂-inv-E : ∀ {i j r} → (T ▷ A ⊢ (i , j) ∈₂ ⟨ r ⟩⁻¹) → (T ▷ A ⊢ (j , i) ∈₂ ⟨ r ⟩)
