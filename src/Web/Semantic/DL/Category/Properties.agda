open import Web.Semantic.DL.ABox.Interp using ( Interp ; _*_ )
open import Web.Semantic.DL.ABox.Interp.Morphism using ( _≲_ )
open import Web.Semantic.DL.ABox.Model using ( _⊨b_ ; ⊨b-resp-≲ )
open import Web.Semantic.DL.Category.Object using 
  ( Object ; IN ; iface )
open import Web.Semantic.DL.Category.Morphism using 
  ( _⇒_ ; BN ; impl ; apply ; apply✓ ; apply-init 
  ; _≣_ ; _⊑_ ; _⊑′_ ; ⊑′-impl-⊑ ; ⊑-impl-⊑′ ; _,_ )
open import Web.Semantic.DL.Category.Composition using
  ( compose ; pipe ; pipe-left ; pipe-right ; _⟫_ ; ⊨b-intro-⟫ )
open import Web.Semantic.DL.Integrity using ( init-≲ )
open import Web.Semantic.DL.KB using ( _,_ )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox ; _,_ )
open import Web.Semantic.Util using
  ( _⊕_⊕_ ; inode ; bnode ; enode ; left ; right )

module Web.Semantic.DL.Category.Properties {Σ : Signature} {S T : TBox Σ} where

compose-resp-⊑′ : ∀ {A B C : Object S T} (F₁ F₂ : A ⇒ B) (G₁ G₂ : B ⇒ C) →
  (F₁ ⊑′ F₂) → (G₁ ⊑′ G₂) → (compose F₁ G₁ ⊑′ compose F₂ G₂)
compose-resp-⊑′ {A} {B} {C} F₁ F₂ G₁ G₂ F₁⊑F₂ G₁⊑G₂ I I⊨STA =
  L⊨F₂⟫G₂ where

  J : Interp Σ (IN A ⊕ BN F₁ ⊕ IN B)
  J = apply F₁ I I⊨STA

  J⊨STB : enode * J ⊨ (S , T) , iface B
  J⊨STB = apply✓ F₁ I I⊨STA

  K : Interp Σ (IN B ⊕ BN G₁ ⊕ IN C)
  K = apply G₁ (enode * J) J⊨STB

  J≲K : enode * J ≲ inode * K
  J≲K = init-≲ (apply-init G₁ (enode * J) J⊨STB)

  L : Interp Σ (IN A ⊕ (BN F₁ ⊕ IN B ⊕ BN G₁) ⊕ IN C)
  L = pipe J K J≲K

  J⊨F₂ : J ⊨b impl F₂
  J⊨F₂ = F₁⊑F₂ I I⊨STA

  K⊨G₂ : K ⊨b impl G₂
  K⊨G₂ = G₁⊑G₂ (enode * J) J⊨STB

  L⊨F₂ : left * L ⊨b impl F₂
  L⊨F₂ = ⊨b-resp-≲ (pipe-left J K J≲K) (impl F₂) J⊨F₂

  L⊨G₂ : right * L ⊨b impl G₂
  L⊨G₂ = ⊨b-resp-≲ (pipe-right J K J≲K) (impl G₂) K⊨G₂

  L⊨F₂⟫G₂ : L ⊨b impl F₂ ⟫ impl G₂
  L⊨F₂⟫G₂ = ⊨b-intro-⟫ L (impl F₂) (impl G₂) L⊨F₂ L⊨G₂

compose-resp-⊑ : ∀ {A B C : Object S T} (F₁ F₂ : A ⇒ B) (G₁ G₂ : B ⇒ C) →
  (F₁ ⊑ F₂) → (G₁ ⊑ G₂) → (compose F₁ G₁ ⊑ compose F₂ G₂)
compose-resp-⊑ F₁ F₂ G₁ G₂ F₁⊑F₂ G₁⊑G₂ =
  ⊑′-impl-⊑ (compose F₁ G₁) (compose F₂ G₂) 
    (compose-resp-⊑′ F₁ F₂ G₁ G₂ 
      (⊑-impl-⊑′ F₁ F₂ F₁⊑F₂) 
      (⊑-impl-⊑′ G₁ G₂ G₁⊑G₂))

compose-resp-≣ : ∀ {A B C : Object S T} {F₁ F₂ : A ⇒ B} {G₁ G₂ : B ⇒ C} →
  (F₁ ≣ F₂) → (G₁ ≣ G₂) → (compose F₁ G₁ ≣ compose F₂ G₂)
compose-resp-≣ {A} {B} {C} {F₁} {F₂} {G₁} {G₂} 
  (F₁⊑F₂ , F₂⊑F₁) (G₁⊑G₂ , G₂⊑G₁) =
    ( compose-resp-⊑ F₁ F₂ G₁ G₂ F₁⊑F₂ G₁⊑G₂ 
    , compose-resp-⊑ F₂ F₁ G₂ G₁ F₂⊑F₁ G₂⊑G₁ )
