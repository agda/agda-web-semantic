open import Data.Product using ( _×_ ; _,_ ; swap )
open import Relation.Nullary using ( ¬_ )
open import Web.Semantic.DL.ABox using ( ABox ; ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.ABox.Model using ( _⊨a_ )
open import Web.Semantic.DL.Concept using
  ( Concept ; ⟨_⟩ ; ¬⟨_⟩ ; ⊤ ; ⊥ ; _⊔_ ; _⊓_ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1 ; >1 ; neg )
open import Web.Semantic.DL.KB using ( KB ; tbox ; abox )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.Role using ( Role ; ⟨_⟩ ; ⟨_⟩⁻¹ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox ; ε ; _,_ ; _⊑₁_ ; _⊑₂_ ; Tra )

module Web.Semantic.DL.Integrity.Closed.Alternate {Σ : Signature} {X : Set} where

-- An alternate definition of closed-world integrity.

infixr 4 _,_
infix 2 _⊫_∈₂_ _⊫_∈₁_ _⊫a_ _⊫t_

data _⊫_∼_ (K : KB Σ X) (x y : X) : Set₁ where
  eq : (∀ I → (I ⊨ K) → (I ⊨a x ∼ y)) → (K ⊫ x ∼ y)

data _⊫_∈₂_ (K : KB Σ X) (xy : X × X) : Role Σ → Set₁ where
  rel : ∀ {r} → (∀ I → (I ⊨ K) → (I ⊨a xy ∈₂ r)) → (K ⊫ xy ∈₂ ⟨ r ⟩)
  rev : ∀ {r} → (∀ I → (I ⊨ K) → (I ⊨a swap xy ∈₂ r)) → (K ⊫ xy ∈₂ ⟨ r ⟩⁻¹)

data _⊫_∈₁_ (K : KB Σ X) (x : X) : Concept Σ → Set₁ where
  +atom : ∀ {c} → (∀ I → (I ⊨ K) → (I ⊨a x ∈₁ c)) → (K ⊫ x ∈₁ ⟨ c ⟩)
  -atom : ∀ {c} → ¬(∀ I → (I ⊨ K) → (I ⊨a x ∈₁ c)) → (K ⊫ x ∈₁ ¬⟨ c ⟩)
  top : (K ⊫ x ∈₁ ⊤)
  inj₁ : ∀ {C D} → (K ⊫ x ∈₁ C) → (K ⊫ x ∈₁ C ⊔ D)
  inj₂ : ∀ {C D} → (K ⊫ x ∈₁ D) → (K ⊫ x ∈₁ C ⊔ D)
  _,_ : ∀ {C D} → (K ⊫ x ∈₁ C) → (K ⊫ x ∈₁ D) → (K ⊫ x ∈₁ C ⊓ D)
  all : ∀ {R C} → (∀ y → (K ⊫ (x , y) ∈₂ R) → (K ⊫ y ∈₁ C)) → (K ⊫ x ∈₁ ∀[ R ] C)
  ex : ∀ {R C} y → (K ⊫ (x , y) ∈₂ R) → (K ⊫ y ∈₁ C) → (K ⊫ x ∈₁ ∃⟨ R ⟩ C)
  uniq : ∀ {R} → (∀ y z → (K ⊫ (x , y) ∈₂ R) → (K ⊫ (x , z) ∈₂ R) → (K ⊫ y ∼ z)) → (K ⊫ x ∈₁ ≤1 R)
  ¬uniq : ∀ {R} y z → (K ⊫ (x , y) ∈₂ R) → (K ⊫ (x , z) ∈₂ R) → ¬(K ⊫ y ∼ z) → (K ⊫ x ∈₁ >1 R)

data _⊫a_ (K : KB Σ X) : ABox Σ X → Set₁ where
  ε : (K ⊫a ε)
  _,_ : ∀ {A B} → (K ⊫a A) → (K ⊫a B) → (K ⊫a A , B)
  eq : ∀ x y → (K ⊫ x ∼ y) → (K ⊫a x ∼ y)
  rl : ∀ xy r → (K ⊫ xy ∈₂ ⟨ r ⟩) → (K ⊫a xy ∈₂ r)
  cn : ∀ x c → (K ⊫ x ∈₁ ⟨ c ⟩) → (K ⊫a x ∈₁ c)

data _⊫t_ (K : KB Σ X) : TBox Σ → Set₁ where
  ε : (K ⊫t ε)
  _,_ : ∀ {T U} → (K ⊫t T) → (K ⊫t U) → (K ⊫t T , U)
  rl : ∀ Q R → (∀ xy → (K ⊫ xy ∈₂ Q) → (K ⊫ xy ∈₂ R)) → (K ⊫t Q ⊑₂ R)
  cn : ∀ C D → (∀ x → (K ⊫ x ∈₁ neg C ⊔ D)) → (K ⊫t C ⊑₁ D)
  tr : ∀ R → (∀ x y z → (K ⊫ (x , y) ∈₂ R) → (K ⊫ (y , z) ∈₂ R) → (K ⊫ (x , z) ∈₂ R)) → (K ⊫t Tra R)

data _⊫k_ (K L : KB Σ X) : Set₁ where
  _,_ : (K ⊫t tbox L) → (K ⊫a abox L) → (K ⊫k L)
