open import Data.Product using ( _×_ ; _,_ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Relation.Unary using ( _∈_ ; _⊆_ )
open import Web.Semantic.DL.Concept.Model using ( _⟦_⟧₁ ; ⟦⟧₁-resp-≈ ; ⟦⟧₁-resp-≃; ⟦⟧₁-refl-≃ )
open import Web.Semantic.DL.Role.Model using ( _⟦_⟧₂ ; ⟦⟧₂-resp-≈ ; ⟦⟧₂-resp-≃ ; ⟦⟧₂-refl-≃ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox ; Axioms ; ε ; _,_ ;_⊑₁_ ; _⊑₂_ )
open import Web.Semantic.DL.TBox.Interp using ( Interp )
open import Web.Semantic.DL.TBox.Interp.Morphism using ( _≃_ ; ≃-sym )
open import Web.Semantic.Util using ( True ; tt ; _∘_ )

module Web.Semantic.DL.TBox.Model {Σ : Signature} where

infixr 2 _⊨t_

_⊨t_ : Interp Σ → TBox Σ → Set
I ⊨t ε        = True
I ⊨t (T , U)  = (I ⊨t T) × (I ⊨t U)
I ⊨t (C ⊑₁ D) = I ⟦ C ⟧₁ ⊆ I ⟦ D ⟧₁
I ⊨t (Q ⊑₂ R) = I ⟦ Q ⟧₂ ⊆ I ⟦ R ⟧₂

Axioms✓ : ∀ I T {t} → (t ∈ Axioms T) → (I ⊨t T) → (I ⊨t t)
Axioms✓ I ε        ()         I⊨T
Axioms✓ I (T , U)  (inj₁ t∈T) (I⊨T , I⊨U) = Axioms✓ I T t∈T I⊨T
Axioms✓ I (T , U)  (inj₂ t∈U) (I⊨T , I⊨U) = Axioms✓ I U t∈U I⊨U
Axioms✓ I (C ⊑₁ D) refl       I⊨T         = I⊨T
Axioms✓ I (Q ⊑₂ R) refl       I⊨T         = I⊨T

⊨t-resp-≃ : ∀ {I J : Interp Σ} → (I ≃ J) → ∀ T → (I ⊨t T) → (J ⊨t T)
⊨t-resp-≃ {I} {J} I≃J ε _ = 
  tt
⊨t-resp-≃ {I} {J} I≃J (T , U) (I⊨T , I⊨U) = 
  (⊨t-resp-≃ I≃J T I⊨T , ⊨t-resp-≃ I≃J U I⊨U)
⊨t-resp-≃ {I} {J} I≃J (C ⊑₁ D) I⊨C⊑D = 
  ⟦⟧₁-refl-≃ I≃J D ∘ I⊨C⊑D ∘ ⟦⟧₁-resp-≃ (≃-sym I≃J) C
⊨t-resp-≃ {I} {J} I≃J (Q ⊑₂ R) I⊨Q⊑R = 
  ⟦⟧₂-refl-≃ I≃J R ∘ I⊨Q⊑R ∘ ⟦⟧₂-resp-≃ (≃-sym I≃J) Q
