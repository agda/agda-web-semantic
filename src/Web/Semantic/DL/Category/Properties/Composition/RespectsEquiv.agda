open import Web.Semantic.DL.ABox.Interp using ( _*_ )
open import Web.Semantic.DL.Category.Object using ( Object )
open import Web.Semantic.DL.Category.Morphism using ( _⇒_ ; _≣_ ; _⊑_ ; _,_ )
open import Web.Semantic.DL.Category.Composition using ( _∙_ )
open import Web.Semantic.DL.Category.Properties.Composition.Lemmas using
  ( compose-left ; compose-mid ; compose-right ; compose-resp-⊨b )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.Util using ( left ; right )

module Web.Semantic.DL.Category.Properties.Composition.RespectsEquiv
  {Σ : Signature} {S T : TBox Σ} where

compose-resp-⊑ : ∀ {A B C : Object S T} (F₁ F₂ : A ⇒ B) (G₁ G₂ : B ⇒ C) → 
  (F₁ ⊑ F₂) → (G₁ ⊑ G₂) → (F₁ ∙ G₁ ⊑ F₂ ∙ G₂)
compose-resp-⊑ F₁ F₂ G₁ G₂ F₁⊑F₂ G₁⊑G₂ I I⊨STA I⊨F₁⟫G₁ = 
  compose-resp-⊨b F₂ G₂ I 
    (F₁⊑F₂ (left * I) I⊨STA 
      (compose-left F₁ G₁ I I⊨F₁⟫G₁)) 
    (G₁⊑G₂ (right * I) (compose-mid F₁ G₁ I I⊨STA I⊨F₁⟫G₁)
      (compose-right F₁ G₁ I I⊨F₁⟫G₁))

compose-resp-≣ : ∀ {A B C : Object S T} {F₁ F₂ : A ⇒ B} {G₁ G₂ : B ⇒ C} → 
  (F₁ ≣ F₂) → (G₁ ≣ G₂) → (F₁ ∙ G₁ ≣ F₂ ∙ G₂)
compose-resp-≣ {A} {B} {C} {F₁} {F₂} {G₁} {G₂}
  (F₁⊑F₂ , F₂⊑F₁) (G₁⊑G₂ , G₂⊑G₁) = 
    ( compose-resp-⊑ F₁ F₂ G₁ G₂ F₁⊑F₂ G₁⊑G₂ 
    , compose-resp-⊑ F₂ F₁ G₂ G₁ F₂⊑F₁ G₂⊑G₁ )
