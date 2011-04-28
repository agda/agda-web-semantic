open import Relation.Binary.PropositionalEquality using ( refl )
open import Web.Semantic.DL.Category.Object using ( Object )
open import Web.Semantic.DL.Category.Morphism using ( _≣_ )
open import Web.Semantic.DL.Category.Composition using ( _∙_ )
open import Web.Semantic.DL.Category.Tensor using ( _⊗_ ; _⟨⊗⟩_ )
open import Web.Semantic.DL.Category.Unit using ( I )
open import Web.Semantic.DL.Category.Wiring using
  ( identity ; symm ; assoc ; assoc⁻¹ ; unit₁ ; unit₁⁻¹ ; unit₂ ; unit₂⁻¹ )
open import Web.Semantic.DL.Category.Properties.Wiring using
  ( rewriting ; rewrite-compose ; rewrite-tensor
  ; rewrite-identity ; rewrite-symm ; rewrite-assoc ; rewrite-assoc⁻¹ 
  ; rewrite-unit₁ ; rewrite-unit₁⁻¹ ; rewrite-unit₂ ; rewrite-unit₂⁻¹ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.Util using ( _≡⊎≡_ )

module Web.Semantic.DL.Category.Properties.Tensor.Isomorphisms
  {Σ : Signature} {S T : TBox Σ} where

symm-iso : ∀ (A₁ A₂ : Object S T) →
  (symm A₁ A₂ ∙ symm A₂ A₁ ≣ identity (A₁ ⊗ A₂))
symm-iso A₁ A₂ =
  rewriting
    (rewrite-compose (rewrite-symm A₁ A₂) (rewrite-symm A₂ A₁))
    ((λ x → refl) ≡⊎≡ (λ x → refl))
    (rewrite-identity (A₁ ⊗ A₂))

assoc-iso : ∀ (A₁ A₂ A₃ : Object S T) →
  (assoc A₁ A₂ A₃ ∙ assoc⁻¹ A₁ A₂ A₃ ≣ identity ((A₁ ⊗ A₂) ⊗ A₃))
assoc-iso A₁ A₂ A₃ = rewriting 
  (rewrite-compose (rewrite-assoc A₁ A₂ A₃) (rewrite-assoc⁻¹ A₁ A₂ A₃)) 
  (((λ x → refl) ≡⊎≡ (λ x → refl)) ≡⊎≡ (λ x → refl))
  (rewrite-identity ((A₁ ⊗ A₂) ⊗ A₃))
  
assoc⁻¹-iso : ∀ (A₁ A₂ A₃ : Object S T) →
  (assoc⁻¹ A₁ A₂ A₃ ∙ assoc A₁ A₂ A₃ ≣ identity (A₁ ⊗ (A₂ ⊗ A₃)))
assoc⁻¹-iso A₁ A₂ A₃ = rewriting 
  (rewrite-compose (rewrite-assoc⁻¹ A₁ A₂ A₃) (rewrite-assoc A₁ A₂ A₃)) 
  ((λ x → refl) ≡⊎≡ ((λ x → refl) ≡⊎≡ (λ x → refl)))
  (rewrite-identity (A₁ ⊗ (A₂ ⊗ A₃)))

unit₁-iso : ∀ (A : Object S T) →
  (unit₁ A ∙ unit₁⁻¹ A ≣ identity (I ⊗ A))
unit₁-iso A = rewriting 
  (rewrite-compose (rewrite-unit₁ A) (rewrite-unit₁⁻¹ A)) 
  ((λ ()) ≡⊎≡ (λ x → refl))
  (rewrite-identity (I ⊗ A))

unit₁⁻¹-iso : ∀ (A : Object S T) →
  (unit₁⁻¹ A ∙ unit₁ A ≣ identity A)
unit₁⁻¹-iso A = rewriting
  (rewrite-compose (rewrite-unit₁⁻¹ A) (rewrite-unit₁ A)) 
  (λ x → refl)
  (rewrite-identity A) 

unit₂-iso : ∀ (A : Object S T) →
  (unit₂ A ∙ unit₂⁻¹ A ≣ identity (A ⊗ I))
unit₂-iso A = rewriting 
  (rewrite-compose (rewrite-unit₂ A) (rewrite-unit₂⁻¹ A)) 
  ((λ x → refl) ≡⊎≡ (λ ()))
  (rewrite-identity (A ⊗ I))

unit₂⁻¹-iso : ∀ (A : Object S T) →
  (unit₂⁻¹ A ∙ unit₂ A ≣ identity A)
unit₂⁻¹-iso A = rewriting
  (rewrite-compose (rewrite-unit₂⁻¹ A) (rewrite-unit₂ A))
  (λ x → refl)
  (rewrite-identity A)
