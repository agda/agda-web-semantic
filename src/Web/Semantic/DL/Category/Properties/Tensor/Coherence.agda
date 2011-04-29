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

module Web.Semantic.DL.Category.Properties.Tensor.Coherence
  {Σ : Signature} {S T : TBox Σ} where

assoc-unit : ∀ (A₁ A₂ : Object S T) →
  (assoc A₁ I A₂ ∙ (identity A₁ ⟨⊗⟩ unit₁ A₂) ≣ unit₂ A₁ ⟨⊗⟩ identity A₂)
assoc-unit A₁ A₂ = rewriting
  (rewrite-compose (rewrite-assoc A₁ I A₂)
    (rewrite-tensor (rewrite-identity A₁) (rewrite-unit₁ A₂)))
  ((λ x → refl) ≡⊎≡ (λ x → refl))
  (rewrite-tensor (rewrite-unit₂ A₁) (rewrite-identity A₂))

assoc-assoc : ∀ (A₁ A₂ A₃ A₄ : Object S T) →
  (assoc (A₁ ⊗ A₂) A₃ A₄ ∙ assoc A₁ A₂ (A₃ ⊗ A₄) ≣ 
    (assoc A₁ A₂ A₃ ⟨⊗⟩ identity A₄) ∙ assoc A₁ (A₂ ⊗ A₃) A₄ ∙ (identity A₁ ⟨⊗⟩ assoc A₂ A₃ A₄))
assoc-assoc A₁ A₂ A₃ A₄ = rewriting
  (rewrite-compose (rewrite-assoc (A₁ ⊗ A₂) A₃ A₄) (rewrite-assoc A₁ A₂ (A₃ ⊗ A₄)))
  ((λ x → refl) ≡⊎≡ ((λ x → refl) ≡⊎≡ ((λ x → refl) ≡⊎≡ (λ x → refl))))
  (rewrite-compose (rewrite-tensor (rewrite-assoc A₁ A₂ A₃) (rewrite-identity A₄)) 
    (rewrite-compose (rewrite-assoc A₁ (A₂ ⊗ A₃) A₄)
      (rewrite-tensor (rewrite-identity A₁) (rewrite-assoc A₂ A₃ A₄))))

assoc-symm : ∀ (A₁ A₂ A₃ : Object S T) →
  (symm (A₁ ⊗ A₂) A₃ ∙ assoc⁻¹ A₃ A₁ A₂ ≣
    assoc A₁ A₂ A₃ ∙ (identity A₁ ⟨⊗⟩ symm A₂ A₃) ∙ assoc⁻¹ A₁ A₃ A₂ ∙ (symm A₁ A₃ ⟨⊗⟩ identity A₂))
assoc-symm A₁ A₂ A₃ = rewriting
  (rewrite-compose (rewrite-symm (A₁ ⊗ A₂) A₃) (rewrite-assoc⁻¹ A₃ A₁ A₂))
  (((λ x → refl) ≡⊎≡ (λ x → refl)) ≡⊎≡ (λ x → refl))
  (rewrite-compose (rewrite-assoc A₁ A₂ A₃)
    (rewrite-compose (rewrite-tensor (rewrite-identity A₁) (rewrite-symm A₂ A₃))
      (rewrite-compose (rewrite-assoc⁻¹ A₁ A₃ A₂)
        (rewrite-tensor (rewrite-symm A₁ A₃) (rewrite-identity A₂)))))

symm-unit : ∀ (A : Object S T) →
  (symm A I ∙ unit₁ A ≣ unit₂ A)
symm-unit A = rewriting
  (rewrite-compose (rewrite-symm A I) (rewrite-unit₁ A))
  (λ x → refl)
  (rewrite-unit₂ A)
