open import Data.Product using ( _×_ ; _,_ )
open import Relation.Nullary using ( ¬_ )
open import Relation.Unary using ( _∈_ ; ∅ ; _∪_ )
open import Web.Semantic.DL.ABox using
  ( ABox ; Assertions ; ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.ABox.Interp using ( Interp ; ⌊_⌋ ; ind )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.Concept using
  ( Concept ; ⟨_⟩ ; ⊤ ; ⊥ ; _⊓_ ; _⊔_ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1 )
open import Web.Semantic.DL.KB using ( KB ; tbox ; abox )
open import Web.Semantic.DL.Role using ( Role ; ⟨_⟩ ; ⟨_⟩⁻¹ )
open import Web.Semantic.DL.TBox using
  ( TBox ; Axioms ; ε ; _,_ ;_⊑₁_ ; _⊑₂_ ; Ref ; Tra )
open import Web.Semantic.DL.TBox.Interp using ( Δ ; _⊨_≈_ ; con ; rol )
open import Web.Semantic.Util using ( _⊕_⊕_ ; inode ; bnode ; enode )

module Web.Semantic.DL.Sequent {Σ : Signature} {W X Y : Set} where

infix 2 _⊕_⊢_∼_ _⊕_⊢_∈₁_ _⊕_⊢_∈₂_

Γ : (Interp Σ X) → (KB Σ (X ⊕ W ⊕ Y)) → Set
Γ I K = Δ ⌊ I ⌋ ⊕ W ⊕ Y

γ : ∀ I K → (X ⊕ W ⊕ Y) → Γ I K
γ I K (inode x) = inode (ind I x)
γ I K (bnode w) = bnode w
γ I K (enode y) = enode y

mutual

  data _⊕_⊢_∼_ I K : Γ I K → Γ I K → Set where
    ∼-assert : ∀ {x y} → ((x ∼ y) ∈ Assertions (abox K)) → (I ⊕ K ⊢ γ I K x ∼ γ I K y)
    ∼-import : ∀ {x y} → (⌊ I ⌋ ⊨ x ≈ y) → (I ⊕ K ⊢ inode x ∼ inode y)
    ∼-refl : ∀ {x} → (I ⊕ K ⊢ x ∼ x)
    ∼-sym : ∀ {x y} → (I ⊕ K ⊢ x ∼ y) → (I ⊕ K ⊢ y ∼ x)
    ∼-trans : ∀ {x y z} → (I ⊕ K ⊢ x ∼ y) → (I ⊕ K ⊢ y ∼ z) → (I ⊕ K ⊢ x ∼ z)
    ∼-≤1 : ∀ {x y z R} → (I ⊕ K ⊢ x ∈₁ (≤1 R)) → (I ⊕ K ⊢ (x , y) ∈₂ R) → (I ⊕ K ⊢ (x , z) ∈₂ R) → (I ⊕ K ⊢ y ∼ z)

  data  _⊕_⊢_∈₁_ I K : Γ I K → Concept Σ → Set where
    ∈₁-assert : ∀ {x c} → ((x ∈₁ c) ∈ Assertions (abox K)) → (I ⊕ K ⊢ γ I K x ∈₁ ⟨ c ⟩)
    ∈₁-import : ∀ {x c} → (x ∈ con ⌊ I ⌋ c) → (I ⊕ K ⊢ inode x ∈₁ ⟨ c ⟩)
    ∈₁-resp-∼ : ∀ {x y C} → (I ⊕ K ⊢ x ∈₁ C) → (I ⊕ K ⊢ x ∼ y) → (I ⊕ K ⊢ y ∈₁ C)
    ∈₁-subsum : ∀ {x C D} → (I ⊕ K ⊢ x ∈₁ C) → ((C ⊑₁ D) ∈ Axioms (tbox K)) → (I ⊕ K ⊢ x ∈₁ D)
    ∈₁-⊤-I : ∀ {x} → (I ⊕ K ⊢ x ∈₁ ⊤)
    ∈₁-⊓-I : ∀ {x C D} → (I ⊕ K ⊢ x ∈₁ C) → (I ⊕ K ⊢ x ∈₁ D) → (I ⊕ K ⊢ x ∈₁ (C ⊓ D))
    ∈₁-⊓-E₁ : ∀ {x C D} → (I ⊕ K ⊢ x ∈₁ (C ⊓ D)) → (I ⊕ K ⊢ x ∈₁ C)
    ∈₁-⊓-E₂ : ∀ {x C D} → (I ⊕ K ⊢ x ∈₁ (C ⊓ D)) → (I ⊕ K ⊢ x ∈₁ D)
    ∈₁-⊔-I₁ : ∀ {x C D} → (I ⊕ K ⊢ x ∈₁ C) → (I ⊕ K ⊢ x ∈₁ (C ⊔ D))
    ∈₁-⊔-I₂ : ∀ {x C D} → (I ⊕ K ⊢ x ∈₁ D) → (I ⊕ K ⊢ x ∈₁ (C ⊔ D))
    ∈₁-∀-E : ∀ {x y R C} → (I ⊕ K ⊢ x ∈₁ (∀[ R ] C)) → (I ⊕ K ⊢ (x , y) ∈₂ R) → (I ⊕ K ⊢ y ∈₁ C)
    ∈₁-∃-I : ∀ {x y R C} → (I ⊕ K ⊢ (x , y) ∈₂ R) → (I ⊕ K ⊢ y ∈₁ C)  → (I ⊕ K ⊢ x ∈₁ (∃⟨ R ⟩ C))

  data _⊕_⊢_∈₂_ I K : (Γ I K × Γ I K) → Role Σ → Set where
    ∈₂-assert : ∀ {x y r} → (((x , y) ∈₂ r) ∈ Assertions (abox K)) → (I ⊕ K ⊢ (γ I K x , γ I K y) ∈₂ ⟨ r ⟩)
    ∈₂-import : ∀ {x y r} → ((x , y) ∈ rol ⌊ I ⌋ r) → (I ⊕ K ⊢ (inode x , inode y) ∈₂ ⟨ r ⟩)
    ∈₂-resp-∼ : ∀ {w x y z R} → (I ⊕ K ⊢ w ∼ x) → (I ⊕ K ⊢ (x , y) ∈₂ R) → (I ⊕ K ⊢ y ∼ z) → (I ⊕ K ⊢ (w , z) ∈₂ R)
    ∈₂-subsum : ∀ {xy R S} → (I ⊕ K ⊢ xy ∈₂ R) → ((R ⊑₂ S) ∈ Axioms (tbox K)) → (I ⊕ K ⊢ xy ∈₂ S)
    ∈₂-refl : ∀ x {R} → ((Ref R) ∈ Axioms (tbox K)) → (I ⊕ K ⊢ (x , x) ∈₂ R)
    ∈₂-trans : ∀ {x y z R} → (I ⊕ K ⊢ (x , y) ∈₂ R) → (I ⊕ K ⊢ (y , z) ∈₂ R) → ((Tra R) ∈ Axioms (tbox K)) → (I ⊕ K ⊢ (x , z) ∈₂ R)
    ∈₂-inv-I : ∀ {x y r} → (I ⊕ K ⊢ (x , y) ∈₂ ⟨ r ⟩) → (I ⊕ K ⊢ (y , x) ∈₂ ⟨ r ⟩⁻¹)
    ∈₂-inv-E : ∀ {x y r} → (I ⊕ K ⊢ (x , y) ∈₂ ⟨ r ⟩⁻¹) → (I ⊕ K ⊢ (y , x) ∈₂ ⟨ r ⟩)
