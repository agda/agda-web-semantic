open import Data.Product using ( _×_ ; _,_ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using
  ( ABox ; Assertions ; ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.Interp using ( Interp ; Δ ; _⊨_≈_ ; ind )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox.Model using ( _⟦_⟧₂ ; _⟦_⟧₁ )
open import Web.Semantic.Util using ( True )

module Web.Semantic.DL.ABox.Model {Σ : Signature} {X : Set} where

infixr 2 _⊨a_

_⟦_⟧₀ : ∀ I → X → Δ I
I ⟦ i ⟧₀ = ind I i

_⊨a_ : Interp Σ X → ABox Σ X → Set
I ⊨a ε            = True
I ⊨a (A , B)      = (I ⊨a A) × (I ⊨a B)
I ⊨a x ∼ y        = I ⊨ I ⟦ x ⟧₀ ≈ I ⟦ y ⟧₀
I ⊨a x ∈₁ C       = I ⟦ x ⟧₀ ∈ I ⟦ C ⟧₁
I ⊨a (x , y) ∈₂ R = (I ⟦ x ⟧₀ , I ⟦ y ⟧₀) ∈ I ⟦ R ⟧₂

Assertions✓ : ∀ I A {a} → (a ∈ Assertions A) → (I ⊨a A) → (I ⊨a a)
Assertions✓ I ε         ()         I⊨A
Assertions✓ I (A , B)   (inj₁ a∈A) (I⊨A , I⊨B) = Assertions✓ I A a∈A I⊨A
Assertions✓ I (A , B)   (inj₂ a∈B) (I⊨A , I⊨B) = Assertions✓ I B a∈B I⊨B
Assertions✓ I (i ∼ j)   refl       I⊨A         = I⊨A
Assertions✓ I (i ∈₁ C)  refl       I⊨A         = I⊨A
Assertions✓ I (ij ∈₂ R) refl       I⊨A         = I⊨A
