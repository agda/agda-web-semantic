open import Data.Product using ( _×_ ; _,_ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Relation.Unary using ( _∈_ ; _⊆_ )
open import Web.Semantic.DL.ABox.Signature using ( Signature ; tsig )
open import Web.Semantic.DL.Concept.Model using ( _⟦_⟧₁ ; ⟦⟧₁-resp-≈ ; ⟦⟧₁-resp-≤≥ )
open import Web.Semantic.DL.Interp using ( Interp ; ≈-sym )
open import Web.Semantic.DL.Interp.Order using ( _≤_ )
open import Web.Semantic.DL.Role.Model using ( _⟦_⟧₂ ; ⟦⟧₂-resp-≈ ; ⟦⟧₂-resp-≤ )
open import Web.Semantic.DL.TBox using ( TBox ; Axioms ; ε ; _,_ ;_⊑₁_ ; _⊑₂_ )
open import Web.Semantic.Util using ( True ; tt ; _∘_ )

module Web.Semantic.DL.TBox.Model {Σ : Signature} {Δ : Set} where

infixr 2 _⊨t_

_⊨t_ : Interp Σ Δ → TBox (tsig Σ) → Set
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

⊨t-resp-≤≥ : ∀ {I J : Interp Σ Δ} → (I ≤ J) → (J ≤ I) → ∀ T → (I ⊨t T) → (J ⊨t T)
⊨t-resp-≤≥ {I} {J} I≤J J≤I ε _ = 
  tt
⊨t-resp-≤≥ {I} {J} I≤J J≤I (T , U) (I⊨T , I⊨U) = 
  (⊨t-resp-≤≥ I≤J J≤I T I⊨T , ⊨t-resp-≤≥ I≤J J≤I U I⊨U)
⊨t-resp-≤≥ {I} {J} I≤J J≤I (C ⊑₁ D) I⊨C⊑D = 
  ⟦⟧₁-resp-≤≥ I≤J J≤I D ∘ I⊨C⊑D ∘ ⟦⟧₁-resp-≤≥ J≤I I≤J C
⊨t-resp-≤≥ {I} {J} I≤J J≤I (Q ⊑₂ R) I⊨Q⊑R = 
  ⟦⟧₂-resp-≤ I≤J R ∘ I⊨Q⊑R ∘ ⟦⟧₂-resp-≤ J≤I Q
