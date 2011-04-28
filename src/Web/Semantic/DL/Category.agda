open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )

import Web.Semantic.DL.Category.Composition
import Web.Semantic.DL.Category.Morphism
import Web.Semantic.DL.Category.Object
import Web.Semantic.DL.Category.Properties
import Web.Semantic.DL.Category.Tensor
import Web.Semantic.DL.Category.Unit
import Web.Semantic.DL.Category.Wiring

module Web.Semantic.DL.Category {Σ : Signature} where

infix 2 _≣_ _⇒_
infixr 5 _∙_ _⊗_ _⟨⊗⟩_

-- Categorial structure

Object : TBox Σ → TBox Σ → Set₁
Object = Web.Semantic.DL.Category.Object.Object

_⇒_ : ∀ {S T} → (Object S T) → (Object S T) → Set₁
_⇒_ = Web.Semantic.DL.Category.Morphism._⇒_

identity : ∀ {S T} (A : Object S T) → (A ⇒ A)
identity = Web.Semantic.DL.Category.Wiring.identity

_∙_ : ∀ {S T} {A B C : Object S T} → (A ⇒ B) → (B ⇒ C) → (A ⇒ C)
_∙_ = Web.Semantic.DL.Category.Composition._∙_

-- Symmetric monoidal structure

I : ∀ {S T} → Object S T
I = Web.Semantic.DL.Category.Unit.I

_⊗_ :  ∀ {S T} → Object S T → Object S T → Object S T
_⊗_ = Web.Semantic.DL.Category.Tensor._⊗_

_⟨⊗⟩_ : ∀ {S T : TBox Σ} {A₁ A₂ B₁ B₂ : Object S T} → 
  (A₁ ⇒ B₁) → (A₂ ⇒ B₂) → ((A₁ ⊗ A₂) ⇒ (B₁ ⊗ B₂))
_⟨⊗⟩_ = Web.Semantic.DL.Category.Tensor._⟨⊗⟩_

symm : ∀ {S T : TBox Σ} → (A B : Object S T) → ((A ⊗ B) ⇒ (B ⊗ A))
symm = Web.Semantic.DL.Category.Wiring.symm

assoc : ∀ {S T : TBox Σ} → (A B C : Object S T) →
  (((A ⊗ B) ⊗ C) ⇒ (A ⊗ (B ⊗ C)))
assoc = Web.Semantic.DL.Category.Wiring.assoc

assoc⁻¹ : ∀ {S T : TBox Σ} → (A B C : Object S T) →
  ((A ⊗ (B ⊗ C)) ⇒ ((A ⊗ B) ⊗ C))
assoc⁻¹ = Web.Semantic.DL.Category.Wiring.assoc⁻¹

unit₁ : ∀ {S T : TBox Σ} (A : Object S T) → ((I ⊗ A) ⇒ A)
unit₁ = Web.Semantic.DL.Category.Wiring.unit₁

unit₁⁻¹ : ∀ {S T : TBox Σ} (A : Object S T) → (A ⇒ (I ⊗ A))
unit₁⁻¹ = Web.Semantic.DL.Category.Wiring.unit₁⁻¹

unit₂ : ∀ {S T : TBox Σ} (A : Object S T) → ((A ⊗ I) ⇒ A)
unit₂ = Web.Semantic.DL.Category.Wiring.unit₂

unit₂⁻¹ : ∀ {S T : TBox Σ} (A : Object S T) → (A ⇒ (A ⊗ I))
unit₂⁻¹ = Web.Semantic.DL.Category.Wiring.unit₂⁻¹

-- Equivalence of morphisms

_≣_ :  ∀ {S T} {A B : Object S T} → (A ⇒ B) → (A ⇒ B) → Set₁
_≣_ = Web.Semantic.DL.Category.Morphism._≣_

≣-refl : ∀ {S T} {A B : Object S T} (F : A ⇒ B) →
  (F ≣ F)
≣-refl = Web.Semantic.DL.Category.Properties.≣-refl

≣-sym :  ∀ {S T} {A B : Object S T} {F G : A ⇒ B} →
  (F ≣ G) → (G ≣ F)
≣-sym = Web.Semantic.DL.Category.Properties.≣-sym

≣-trans :  ∀ {S T} {A B : Object S T} {F G H : A ⇒ B} → 
  (F ≣ G) → (G ≣ H) → (F ≣ H)
≣-trans = Web.Semantic.DL.Category.Properties.≣-trans

-- Equations of a category

compose-resp-≣ : ∀ {S T} {A B C : Object S T} (F₁ F₂ : A ⇒ B) (G₁ G₂ : B ⇒ C) →
  (F₁ ≣ F₂) → (G₁ ≣ G₂) → (F₁ ∙ G₁ ≣ F₂ ∙ G₂)
compose-resp-≣ = Web.Semantic.DL.Category.Properties.compose-resp-≣

compose-unit₁ : ∀ {S T} {A B C : Object S T} (F : A ⇒ B) →
  (identity A ∙ F ≣ F)
compose-unit₁ = Web.Semantic.DL.Category.Properties.compose-unit₁

compose-unit₂ : ∀ {S T} {A B C : Object S T} (F : A ⇒ B) →
  (F ∙ identity B ≣ F)
compose-unit₂ = Web.Semantic.DL.Category.Properties.compose-unit₂

compose-assoc : ∀ {S T} {A B C D : Object S T} 
  (F : A ⇒ B) (G : B ⇒ C) (H : C ⇒ D) →
    ((F ∙ G) ∙ H ≣ F ∙ (G ∙ H))
compose-assoc = Web.Semantic.DL.Category.Properties.compose-assoc

-- Equations of a symmetric monoidal category

tensor-resp-≣ : ∀ {S T} {A₁ A₂ B₁ B₂ : Object S T} 
  (F₁ G₁ : A₁ ⇒ B₁) (F₂ G₂ : A₂ ⇒ B₂) → 
    (F₁ ≣ G₁) → (F₂ ≣ G₂) → (F₁ ⟨⊗⟩ F₂ ≣ G₁ ⟨⊗⟩ G₂)
tensor-resp-≣ = Web.Semantic.DL.Category.Properties.tensor-resp-≣

tensor-resp-compose : ∀ {S T} {A₁ A₂ B₁ B₂ C₁ C₂ : Object S T}
  (F₁ : A₁ ⇒ B₁) (F₂ : A₂ ⇒ B₂) (G₁ : B₁ ⇒ C₁) (G₂ : B₂ ⇒ C₂) →
    (((F₁ ∙ G₁) ⟨⊗⟩ (F₂ ∙ G₂)) ≣ ((F₁ ⟨⊗⟩ F₂) ∙ (G₁ ⟨⊗⟩ G₂)))
tensor-resp-compose = Web.Semantic.DL.Category.Properties.tensor-resp-compose

tensor-resp-id : ∀ {S T} (A₁ A₂ : Object S T) →
  ((identity A₁ ⟨⊗⟩ identity A₂) ≣ identity (A₁ ⊗ A₂))
tensor-resp-id = Web.Semantic.DL.Category.Properties.tensor-resp-id

symm-iso : ∀ {S T} (A₁ A₂ : Object S T) →
  (symm A₁ A₂ ∙ symm A₂ A₁ ≣ identity (A₁ ⊗ A₂))
symm-iso = Web.Semantic.DL.Category.Properties.symm-iso

assoc-iso : ∀ {S T} (A₁ A₂ A₃ : Object S T) →
  (assoc A₁ A₂ A₃ ∙ assoc⁻¹ A₁ A₂ A₃ ≣ identity ((A₁ ⊗ A₂) ⊗ A₃))
assoc-iso = Web.Semantic.DL.Category.Properties.assoc-iso

assoc⁻¹-iso : ∀ {S T} (A₁ A₂ A₃ : Object S T) →
  (assoc⁻¹ A₁ A₂ A₃ ∙ assoc A₁ A₂ A₃ ≣ identity (A₁ ⊗ (A₂ ⊗ A₃)))
assoc⁻¹-iso = Web.Semantic.DL.Category.Properties.assoc⁻¹-iso

unit₁-iso : ∀ {S T} (A : Object S T) →
  (unit₁ A ∙ unit₁⁻¹ A ≣ identity (I ⊗ A))
unit₁-iso = Web.Semantic.DL.Category.Properties.unit₁-iso

unit₁⁻¹-iso : ∀ {S T} (A : Object S T) →
  (unit₁⁻¹ A ∙ unit₁ A ≣ identity A)
unit₁⁻¹-iso = Web.Semantic.DL.Category.Properties.unit₁⁻¹-iso

unit₂-iso : ∀ {S T} (A : Object S T) →
  (unit₂ A ∙ unit₂⁻¹ A ≣ identity (A ⊗ I))
unit₂-iso = Web.Semantic.DL.Category.Properties.unit₂-iso

unit₂⁻¹-iso : ∀ {S T} (A : Object S T) →
  (unit₂⁻¹ A ∙ unit₂ A ≣ identity A)
unit₂⁻¹-iso = Web.Semantic.DL.Category.Properties.unit₂⁻¹-iso

assoc-unit : ∀ {S T} (A₁ A₂ : Object S T) →
  (assoc A₁ I A₂ ∙ (identity A₁ ⟨⊗⟩ unit₁ A₂) ≣ unit₂ A₁ ⟨⊗⟩ identity A₂)
assoc-unit = Web.Semantic.DL.Category.Properties.assoc-unit

assoc-assoc : ∀ {S T} (A₁ A₂ A₃ A₄ : Object S T) →
  (assoc (A₁ ⊗ A₂) A₃ A₄ ∙ assoc A₁ A₂ (A₃ ⊗ A₄) ≣ 
    (assoc A₁ A₂ A₃ ⟨⊗⟩ identity A₄) ∙ assoc A₁ (A₂ ⊗ A₃) A₄ ∙ (identity A₁ ⟨⊗⟩ assoc A₂ A₃ A₄))
assoc-assoc = Web.Semantic.DL.Category.Properties.assoc-assoc

assoc-symm : ∀ {S T} (A₁ A₂ A₃ : Object S T) →
  (symm (A₁ ⊗ A₂) A₃ ∙ assoc⁻¹ A₃ A₁ A₂ ≣
    assoc A₁ A₂ A₃ ∙ (identity A₁ ⟨⊗⟩ symm A₂ A₃) ∙ assoc⁻¹ A₁ A₃ A₂ ∙ (symm A₁ A₃ ⟨⊗⟩ identity A₂))
assoc-symm = Web.Semantic.DL.Category.Properties.assoc-symm

unit₁-natural : ∀ {S T} {A B : Object S T} (F : A ⇒ B) →
  ((identity I ⟨⊗⟩ F) ∙ unit₁ B ≣ unit₁ A ∙ F)
unit₁-natural = Web.Semantic.DL.Category.Properties.unit₁-natural

