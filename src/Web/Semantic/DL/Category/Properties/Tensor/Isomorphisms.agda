open import Data.Sum using ( inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Web.Semantic.DL.Category.Object using ( Object )
open import Web.Semantic.DL.Category.Morphism using ( _≣_ )
open import Web.Semantic.DL.Category.Composition using ( _∙_ )
open import Web.Semantic.DL.Category.Tensor using ( _⊗_ ; _⟨⊗⟩_ )
open import Web.Semantic.DL.Category.Unit using ( I )
open import Web.Semantic.DL.Category.Wiring using
  ( identity ; symm ; assoc ; assoc⁻¹ ; unit₁ ; unit₁⁻¹ ; unit₂ ; unit₂⁻¹ 
  ; id✓ ; ⊎-swap✓ ; ⊎-assoc⁻¹✓ ; ⊎-assoc✓
  ; inj₁✓ ; inj₂✓ ; ⊎-unit₁✓ ; ⊎-unit₂✓ )
open import Web.Semantic.DL.Category.Properties.Composition.RespectsWiring using
  ( compose-resp-wiring )
open import Web.Semantic.DL.Category.Properties.Tensor.RespectsWiring using
  ( tensor-resp-wiring )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.Util using 
  ( id ; inj⁻¹ ; ⊎-swap ; ⊎-assoc ; ⊎-assoc⁻¹ ; ⊎-unit₁ ; ⊎-unit₂
  ; ⊎-swap-iso ; ⊎-assoc-iso ; ⊎-assoc⁻¹-iso ; ⊎-unit₁-iso ; ⊎-unit₂-iso )

module Web.Semantic.DL.Category.Properties.Tensor.Isomorphisms
  {Σ : Signature} {S T : TBox Σ} where

symm-iso : ∀ (A₁ A₂ : Object S T) →
  (symm A₁ A₂ ∙ symm A₂ A₁ ≣ identity (A₁ ⊗ A₂))
symm-iso A₁ A₂ =
  compose-resp-wiring (A₁ ⊗ A₂) (A₂ ⊗ A₁) (A₁ ⊗ A₂) 
    ⊎-swap (⊎-swap✓ A₁ A₂) ⊎-swap (⊎-swap✓ A₂ A₁) id (id✓ (A₁ ⊗ A₂))
    ⊎-swap-iso

assoc-iso : ∀ (A₁ A₂ A₃ : Object S T) →
  (assoc A₁ A₂ A₃ ∙ assoc⁻¹ A₁ A₂ A₃ ≣ identity ((A₁ ⊗ A₂) ⊗ A₃))
assoc-iso A₁ A₂ A₃ = 
  compose-resp-wiring ((A₁ ⊗ A₂) ⊗ A₃) (A₁ ⊗ (A₂ ⊗ A₃)) ((A₁ ⊗ A₂) ⊗ A₃) 
    ⊎-assoc⁻¹ (⊎-assoc⁻¹✓ A₁ A₂ A₃) ⊎-assoc (⊎-assoc✓ A₁ A₂ A₃) id (id✓ ((A₁ ⊗ A₂) ⊗ A₃)) 
    ⊎-assoc⁻¹-iso

assoc⁻¹-iso : ∀ (A₁ A₂ A₃ : Object S T) →
  (assoc⁻¹ A₁ A₂ A₃ ∙ assoc A₁ A₂ A₃ ≣ identity (A₁ ⊗ (A₂ ⊗ A₃)))
assoc⁻¹-iso A₁ A₂ A₃ = 
  compose-resp-wiring (A₁ ⊗ (A₂ ⊗ A₃)) ((A₁ ⊗ A₂) ⊗ A₃) (A₁ ⊗ (A₂ ⊗ A₃))
    ⊎-assoc (⊎-assoc✓ A₁ A₂ A₃) ⊎-assoc⁻¹ (⊎-assoc⁻¹✓ A₁ A₂ A₃) id (id✓ (A₁ ⊗ (A₂ ⊗ A₃)) )
    ⊎-assoc-iso

unit₁-iso : ∀ (A : Object S T) →
  (unit₁ A ∙ unit₁⁻¹ A ≣ identity (I ⊗ A))
unit₁-iso A = 
  compose-resp-wiring (I ⊗ A) A (I ⊗ A)
    inj₂ (inj₂✓ A) ⊎-unit₁ (⊎-unit₁✓ A) id (id✓ (I ⊗ A))
    ⊎-unit₁-iso

unit₁⁻¹-iso : ∀ (A : Object S T) →
  (unit₁⁻¹ A ∙ unit₁ A ≣ identity A)
unit₁⁻¹-iso A = 
  compose-resp-wiring A (I ⊗ A) A
    ⊎-unit₁ (⊎-unit₁✓ A) inj₂ (inj₂✓ A) id (id✓ A)
    (λ x → refl)

unit₂-iso : ∀ (A : Object S T) →
  (unit₂ A ∙ unit₂⁻¹ A ≣ identity (A ⊗ I))
unit₂-iso A = 
  compose-resp-wiring (A ⊗ I) A (A ⊗ I)
    inj₁ (inj₁✓ A) ⊎-unit₂ (⊎-unit₂✓ A) id (id✓ (A ⊗ I))
    ⊎-unit₂-iso

unit₂⁻¹-iso : ∀ (A : Object S T) →
  (unit₂⁻¹ A ∙ unit₂ A ≣ identity A)
unit₂⁻¹-iso A = 
  compose-resp-wiring A (A ⊗ I) A
    ⊎-unit₂ (⊎-unit₂✓ A) inj₁ (inj₁✓ A) id (id✓ A)
    (λ x → refl)
