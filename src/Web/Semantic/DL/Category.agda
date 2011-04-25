open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )

import Web.Semantic.DL.Category.Object
import Web.Semantic.DL.Category.Morphism
import Web.Semantic.DL.Category.Wiring
import Web.Semantic.DL.Category.Composition
import Web.Semantic.DL.Category.IsCategory

module Web.Semantic.DL.Category {Σ : Signature} where

infix 2 _≣_ _⇒_
infixr 5 _∙_

-- Gadgets of a category

Object : TBox Σ → TBox Σ → Set₁
Object = Web.Semantic.DL.Category.Object.Object

_⇒_ : ∀ {S T} → (Object S T) → (Object S T) → Set₁
_⇒_ = Web.Semantic.DL.Category.Morphism._⇒_

identity : ∀ {S T} (A : Object S T) → (A ⇒ A)
identity = Web.Semantic.DL.Category.Wiring.identity

_∙_ : ∀ {S T} {A B C : Object S T} → (A ⇒ B) → (B ⇒ C) → (A ⇒ C)
_∙_ = Web.Semantic.DL.Category.Composition._∙_

-- Equivalence of morphisms

_≣_ :  ∀ {S T} {A B : Object S T} → (A ⇒ B) → (A ⇒ B) → Set₁
_≣_ = Web.Semantic.DL.Category.Morphism._≣_

≣-refl : ∀ {S T} {A B : Object S T} (F : A ⇒ B) →
  (F ≣ F)
≣-refl = Web.Semantic.DL.Category.IsCategory.≣-refl

≣-sym :  ∀ {S T} {A B : Object S T} {F G : A ⇒ B} →
  (F ≣ G) → (G ≣ F)
≣-sym = Web.Semantic.DL.Category.IsCategory.≣-sym

≣-trans :  ∀ {S T} {A B : Object S T} {F G H : A ⇒ B} → 
  (F ≣ G) → (G ≣ H) → (F ≣ H)
≣-trans = Web.Semantic.DL.Category.IsCategory.≣-trans

-- Equations of a category

compose-resp-≣ : ∀ {S T} {A B C : Object S T} (F₁ F₂ : A ⇒ B) (G₁ G₂ : B ⇒ C) →
  (F₁ ≣ F₂) → (G₁ ≣ G₂) → (F₁ ∙ G₁ ≣ F₂ ∙ G₂)
compose-resp-≣ = Web.Semantic.DL.Category.IsCategory.compose-resp-≣

compose-unit₁ : ∀ {S T} {A B C : Object S T} (F : A ⇒ B) →
  (identity A ∙ F ≣ F)
compose-unit₁ = Web.Semantic.DL.Category.IsCategory.compose-unit₁

compose-unit₂ : ∀ {S T} {A B C : Object S T} (F : A ⇒ B) →
  (F ∙ identity B ≣ F)
compose-unit₂ = Web.Semantic.DL.Category.IsCategory.compose-unit₂

compose-assoc : ∀ {S T} {A B C D : Object S T} 
  (F : A ⇒ B) (G : B ⇒ C) (H : C ⇒ D) →
    ((F ∙ G) ∙ H ≣ F ∙ (G ∙ H))
compose-assoc = Web.Semantic.DL.Category.IsCategory.compose-assoc
