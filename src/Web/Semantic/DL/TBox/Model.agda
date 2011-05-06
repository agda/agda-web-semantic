open import Data.Product using ( _×_ ; _,_ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Relation.Unary using ( _∈_ ; _∉_ ; _⊆_ )
open import Web.Semantic.DL.Concept.Model using
  ( _⟦_⟧₁ ; ⟦⟧₁-resp-≈ ; ⟦⟧₁-resp-≃; ⟦⟧₁-refl-≃ )
open import Web.Semantic.DL.Role.Model using
  ( _⟦_⟧₂ ; ⟦⟧₂-resp-≈ ; ⟦⟧₂-resp-≃ ; ⟦⟧₂-refl-≃ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using
  ( TBox ; Axioms ; ε ; _,_ ;_⊑₁_ ; _⊑₂_ ; Dis ; Ref ; Irr ; Tra )
open import Web.Semantic.DL.TBox.Interp using ( Interp )
open import Web.Semantic.DL.TBox.Interp.Morphism using ( _≃_ ; ≃-sym )
open import Web.Semantic.Util using ( True ; tt ; _∘_ )

module Web.Semantic.DL.TBox.Model {Σ : Signature} where

infixr 2 _⊨t_

_⊨t_ : Interp Σ → TBox Σ → Set
I ⊨t ε         = True
I ⊨t (T , U)   = (I ⊨t T) × (I ⊨t U)
I ⊨t (C ⊑₁ D)  = I ⟦ C ⟧₁ ⊆ I ⟦ D ⟧₁
I ⊨t (Q ⊑₂ R)  = I ⟦ Q ⟧₂ ⊆ I ⟦ R ⟧₂
I ⊨t (Dis Q R) = ∀ {xy} → (xy ∈ I ⟦ Q ⟧₂) → (xy ∉ I ⟦ R ⟧₂)
I ⊨t (Ref R)   = ∀ x → ((x , x) ∈ I ⟦ R ⟧₂) 
I ⊨t (Irr R)   = ∀ x → ((x , x) ∉ I ⟦ R ⟧₂) 
I ⊨t (Tra R)   = ∀ {x y z} → 
  ((x , y) ∈ I ⟦ R ⟧₂) → ((y , z) ∈ I ⟦ R ⟧₂) → ((x , z) ∈ I ⟦ R ⟧₂)

Axioms✓ : ∀ I T {t} → (t ∈ Axioms T) → (I ⊨t T) → (I ⊨t t)
Axioms✓ I ε         ()         I⊨T
Axioms✓ I (T , U)   (inj₁ t∈T) (I⊨T , I⊨U) = Axioms✓ I T t∈T I⊨T
Axioms✓ I (T , U)   (inj₂ t∈U) (I⊨T , I⊨U) = Axioms✓ I U t∈U I⊨U
Axioms✓ I (C ⊑₁ D)  refl       I⊨T         = I⊨T
Axioms✓ I (Q ⊑₂ R)  refl       I⊨T         = I⊨T
Axioms✓ I (Dis Q R) refl       I⊨T         = I⊨T
Axioms✓ I (Ref R)   refl       I⊨T         = I⊨T
Axioms✓ I (Irr R)   refl       I⊨T         = I⊨T
Axioms✓ I (Tra R)   refl       I⊨T         = I⊨T

⊨t-resp-≃ : ∀ {I J : Interp Σ} → (I ≃ J) → ∀ T → (I ⊨t T) → (J ⊨t T)
⊨t-resp-≃ {I} {J} I≃J ε _ = 
  tt
⊨t-resp-≃ {I} {J} I≃J (T , U) (I⊨T , I⊨U) = 
  (⊨t-resp-≃ I≃J T I⊨T , ⊨t-resp-≃ I≃J U I⊨U)
⊨t-resp-≃ {I} {J} I≃J (C ⊑₁ D) I⊨C⊑D = 
  ⟦⟧₁-refl-≃ I≃J D ∘ I⊨C⊑D ∘ ⟦⟧₁-resp-≃ (≃-sym I≃J) C
⊨t-resp-≃ {I} {J} I≃J (Q ⊑₂ R) I⊨Q⊑R = ⟦⟧₂-refl-≃ I≃J R ∘ I⊨Q⊑R ∘
  ⟦⟧₂-resp-≃ (≃-sym I≃J) Q
⊨t-resp-≃ {I} {J} I≃J (Dis Q R) I⊨DisQR = λ xy∈⟦Q⟧ xy∈⟦R⟧ → 
  I⊨DisQR (⟦⟧₂-resp-≃ (≃-sym I≃J) Q xy∈⟦Q⟧) (⟦⟧₂-resp-≃ (≃-sym I≃J) R xy∈⟦R⟧)
⊨t-resp-≃ {I} {J} I≃J (Ref R) I⊨RefR = λ x → ⟦⟧₂-refl-≃ I≃J R (I⊨RefR _)
⊨t-resp-≃ {I} {J} I≃J (Irr R) I⊨IrrR = λ x xx∈⟦R⟧ → 
  I⊨IrrR _ (⟦⟧₂-resp-≃ (≃-sym I≃J) R xx∈⟦R⟧)
⊨t-resp-≃ {I} {J} I≃J (Tra R) I⊨TraR = λ xy∈⟦R⟧ yz∈⟦R⟧ → 
  ⟦⟧₂-refl-≃ I≃J R (I⊨TraR 
    (⟦⟧₂-resp-≃ (≃-sym I≃J) R xy∈⟦R⟧) 
    (⟦⟧₂-resp-≃ (≃-sym I≃J) R yz∈⟦R⟧))
