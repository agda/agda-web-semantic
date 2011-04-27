open import Data.Product using ( _,_ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Web.Semantic.DL.ABox.Interp using ( _*_ )
open import Web.Semantic.DL.ABox.Model using ( *-resp-⟨ABox⟩ )
open import Web.Semantic.DL.Category.Object using ( Object ; iface )
open import Web.Semantic.DL.Category.Morphism using ( _⇒_ ; _≣_ ; _⊑_ ; _,_ )
open import Web.Semantic.DL.Category.Tensor using ( _⟨⊗⟩_ )
open import Web.Semantic.DL.Category.Properties.Tensor.Lemmas using
  ( tensor-up ; tensor-down ; tensor-resp-⊨b )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.Util using ( inode ; up ; down )

module Web.Semantic.DL.Category.Properties.Tensor.RespectsEquiv
  {Σ : Signature} {S T : TBox Σ} where

tensor-resp-⊑ : ∀ {A₁ A₂ B₁ B₂ : Object S T}
  (F₁ G₁ : A₁ ⇒ B₁) (F₂ G₂ : A₂ ⇒ B₂) → 
    (F₁ ⊑ G₁) → (F₂ ⊑ G₂) → (F₁ ⟨⊗⟩ F₂ ⊑ G₁ ⟨⊗⟩ G₂)
tensor-resp-⊑ {A₁} {A₂} F₁ G₁ F₂ G₂ F₁⊑G₁ F₂⊑G₂ 
  I (I⊨ST , (I⊨A₁ , I⊨A₂)) I⊨F₁F₂ = 
    tensor-resp-⊨b G₁ G₂ I 
      (F₁⊑G₁ (up * I) 
        (I⊨ST , *-resp-⟨ABox⟩ inj₁ (inode * I) (iface A₁) I⊨A₁) 
        (tensor-up F₁ F₂ I I⊨F₁F₂))
      (F₂⊑G₂ (down * I) 
        (I⊨ST , *-resp-⟨ABox⟩ inj₂ (inode * I) (iface A₂) I⊨A₂) 
        (tensor-down F₁ F₂ I I⊨F₁F₂)) 

tensor-resp-≣ : ∀ {A₁ A₂ B₁ B₂ : Object S T}
  (F₁ G₁ : A₁ ⇒ B₁) (F₂ G₂ : A₂ ⇒ B₂) → 
    (F₁ ≣ G₁) → (F₂ ≣ G₂) → (F₁ ⟨⊗⟩ F₂ ≣ G₁ ⟨⊗⟩ G₂)
tensor-resp-≣ F₁ G₁ F₂ G₂ (F₁⊑G₁ , G₁⊑F₁) (F₂⊑G₂ , G₂⊑F₂) = 
  ( tensor-resp-⊑ F₁ G₁ F₂ G₂ F₁⊑G₁ F₂⊑G₂
  , tensor-resp-⊑ G₁ F₁ G₂ F₂ G₁⊑F₁ G₂⊑F₂ )
