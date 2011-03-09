open import Data.Product using ( _×_ ; _,_ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox ; Assertions ; ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.ABox.Signature using ( Signature ; IN )
open import Web.Semantic.DL.Concept.Model using ( _⟦_⟧₁ ; ⟦⟧₁-resp-≈ ; ⟦⟧₁-resp-≤≥ )
open import Web.Semantic.DL.Interp using ( Interp ; _⊨_≈_ ; ind ; ≈-refl ; ≈-sym ; ≈-trans )
open import Web.Semantic.DL.Interp.Order using ( _≤_ ; ≤-resp-ind ; ≤-resp-≈ )
open import Web.Semantic.DL.Role.Model using ( _⟦_⟧₂ ; ⟦⟧₂-resp-≈ ; ⟦⟧₂-resp-≤ )
open import Web.Semantic.Util using ( True ; tt )

module Web.Semantic.DL.ABox.Model {Σ : Signature} {Δ : Set} where

infixr 2 _⊨a_

_⟦_⟧₀ : ∀ I → (IN Σ) → Δ
I ⟦ i ⟧₀ = ind I i

_⊨a_ : Interp Σ Δ → ABox Σ → Set
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

⊨a-resp-≤≥ : ∀ {I J : Interp Σ Δ} → (I ≤ J) → (J ≤ I) → ∀ A → (I ⊨a A) → (J ⊨a A)
⊨a-resp-≤≥ {I} {J} I≤J J≤I ε I⊨A = 
  tt
⊨a-resp-≤≥ {I} {J} I≤J J≤I (A , B) (I⊨A , I⊨B) = 
  (⊨a-resp-≤≥ I≤J J≤I A I⊨A , ⊨a-resp-≤≥ I≤J J≤I B I⊨B)
⊨a-resp-≤≥ {I} {J} I≤J J≤I (x ∼ y)   I⊨x∼y = 
  ≈-trans J (≈-sym J (≤-resp-ind I≤J)) (≈-trans J (≤-resp-≈ I≤J I⊨x∼y) (≤-resp-ind I≤J))
⊨a-resp-≤≥ {I} {J} I≤J J≤I (x ∈₁ C)  I⊨x∈C = 
  ⟦⟧₁-resp-≈ J C (⟦⟧₁-resp-≤≥ I≤J J≤I C I⊨x∈C) (≤-resp-ind I≤J)
⊨a-resp-≤≥ {I} {J} I≤J J≤I ((x , y) ∈₂ R) I⊨xy∈R = 
  ⟦⟧₂-resp-≈ J R (≈-sym J (≤-resp-ind I≤J)) (⟦⟧₂-resp-≤ I≤J R I⊨xy∈R) (≤-resp-ind I≤J)
