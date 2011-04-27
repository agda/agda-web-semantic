open import Data.Product using ( _,_ )
open import Data.Sum using ( _⊎_ )
open import Web.Semantic.DL.ABox.Interp using ( Interp ; _*_ )
open import Web.Semantic.DL.ABox.Model using ( _⊨a_ ; _⊨b_ ; *-resp-⟨ABox⟩ )
open import Web.Semantic.DL.Category.Object using ( Object ; IN )
open import Web.Semantic.DL.Category.Morphism using ( _⇒_ ; BN ; impl )
open import Web.Semantic.DL.Category.Tensor using
  ( _⟨⊗⟩_ ; ⊨a-intro-⟨&⟩ ; ⊨b-intro-⟨&⟩ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.Util using ( _⊕_⊕_ ; up ; down )

module Web.Semantic.DL.Category.Properties.Tensor.Lemmas 
  {Σ : Signature} {S T : TBox Σ} where

tensor-up : ∀ {A₁ A₂ B₁ B₂ : Object S T} (F₁ : A₁ ⇒ B₁) (F₂ : A₂ ⇒ B₂) I → 
  (I ⊨a impl (F₁ ⟨⊗⟩ F₂)) → (up * I ⊨a impl F₁)
tensor-up F₁ F₂ I (I⊨F₁ , I⊨F₂) = *-resp-⟨ABox⟩ up I (impl F₁) I⊨F₁

tensor-down : ∀ {A₁ A₂ B₁ B₂ : Object S T} (F₁ : A₁ ⇒ B₁) (F₂ : A₂ ⇒ B₂) I → 
  (I ⊨a impl (F₁ ⟨⊗⟩ F₂)) → (down * I ⊨a impl F₂)
tensor-down F₁ F₂ I (I⊨F₁ , I⊨F₂) = *-resp-⟨ABox⟩ down I (impl F₂) I⊨F₂

tensor-resp-⊨a : ∀ {A₁ A₂ B₁ B₂ : Object S T}
  (F₁ : A₁ ⇒ B₁) (F₂ : A₂ ⇒ B₂) →
    (I : Interp Σ ((IN A₁ ⊎ IN A₂) ⊕ (BN F₁ ⊎ BN F₂) ⊕ (IN B₁ ⊎ IN B₂))) →
      (up * I ⊨a impl F₁) → (down * I ⊨a impl F₂) → (I ⊨a impl (F₁ ⟨⊗⟩ F₂))
tensor-resp-⊨a F₁ F₂ I I₁⊨F₁ I₂⊨F₂ =
  ⊨a-intro-⟨&⟩ I (impl F₁) (impl F₂) I₁⊨F₁ I₂⊨F₂

tensor-resp-⊨b : ∀ {V₁ V₂} {A₁ A₂ B₁ B₂ : Object S T} 
  (F₁ : A₁ ⇒ B₁) (F₂ : A₂ ⇒ B₂) →
    (I : Interp Σ ((IN A₁ ⊎ IN A₂) ⊕ (V₁ ⊎ V₂) ⊕ (IN B₁ ⊎ IN B₂))) →
      (up * I ⊨b impl F₁) → (down * I ⊨b impl F₂) → (I ⊨b impl (F₁ ⟨⊗⟩ F₂))
tensor-resp-⊨b F₁ F₂ I I⊨F₁ I⊨F₂ =
  ⊨b-intro-⟨&⟩ I (impl F₁) (impl F₂) I⊨F₁ I⊨F₂
