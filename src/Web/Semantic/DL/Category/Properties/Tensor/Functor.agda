open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Web.Semantic.DL.ABox.Interp using ( ⌊_⌋ ; ind ; _*_ )
open import Web.Semantic.DL.ABox.Model using
  ( _⊨a_ ; ⊨a-resp-≡³ ; on-bnode ; bnodes ; _,_ )
open import Web.Semantic.DL.Category.Object using ( Object ; IN )
open import Web.Semantic.DL.Category.Morphism using
  ( _⇒_ ; BN ; impl ; _⊑_ ; _≣_ ; _,_ )
open import Web.Semantic.DL.Category.Composition using ( _∙_ )
open import Web.Semantic.DL.Category.Tensor using ( _⊗_ ; _⟨⊗⟩_ )
open import Web.Semantic.DL.Category.Wiring using ( identity ; id✓ )
open import Web.Semantic.DL.Category.Properties.Composition.Lemmas using
  ( compose-left ; compose-right ; compose-resp-⊨a )
open import Web.Semantic.DL.Category.Properties.Tensor.Lemmas using
  ( tensor-up ; tensor-down ; tensor-resp-⊨a )
open import Web.Semantic.DL.Category.Properties.Tensor.RespectsWiring using
  ( tensor-resp-wiring )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.DL.TBox.Interp using ( Δ )
open import Web.Semantic.Util using
  ( id ; _∘_ ; _⊕_⊕_ ; inode ; bnode ; enode ; left ; right ; up ; down )

module Web.Semantic.DL.Category.Properties.Tensor.Functor
  {Σ : Signature} {S T : TBox Σ} where

tensor-resp-id : ∀ (A₁ A₂ : Object S T) →
  ((identity A₁ ⟨⊗⟩ identity A₂) ≣ identity (A₁ ⊗ A₂))
tensor-resp-id A₁ A₂ = 
  tensor-resp-wiring A₁ A₂ A₁ A₂ 
    id (id✓ A₁) id (id✓ A₂) id (id✓ (A₁ ⊗ A₂))
    (λ x → refl) (λ x → refl)

tensor-resp-compose :  ∀ {A₁ A₂ B₁ B₂ C₁ C₂ : Object S T}
  (F₁ : A₁ ⇒ B₁) (F₂ : A₂ ⇒ B₂) (G₁ : B₁ ⇒ C₁) (G₂ : B₂ ⇒ C₂) →
    (((F₁ ∙ G₁) ⟨⊗⟩ (F₂ ∙ G₂)) ≣ ((F₁ ⟨⊗⟩ F₂) ∙ (G₁ ⟨⊗⟩ G₂)))
tensor-resp-compose {A₁} {A₂} {B₁} {B₂} {C₁} {C₂} F₁ F₂ G₁ G₂ = 
  (LHS⊑RHS , RHS⊑LHS) where

  LHS⊑RHS : (F₁ ∙ G₁) ⟨⊗⟩ (F₂ ∙ G₂) ⊑ (F₁ ⟨⊗⟩ F₂) ∙ (G₁ ⟨⊗⟩ G₂)
  LHS⊑RHS I I⊨STA₁A₂ I⊨LHS = (f , I⊨RHS) where

    f : ((BN F₁ ⊎ BN F₂) ⊕ (IN B₁ ⊎ IN B₂) ⊕ (BN G₁ ⊎ BN G₂)) → Δ ⌊ I ⌋
    f (inode (inj₁ v)) = ind I (bnode (inj₁ (inode v)))
    f (inode (inj₂ v)) = ind I (bnode (inj₂ (inode v)))
    f (bnode (inj₁ y)) = ind I (bnode (inj₁ (bnode y)))
    f (bnode (inj₂ y)) = ind I (bnode (inj₂ (bnode y)))
    f (enode (inj₁ w)) = ind I (bnode (inj₁ (enode w)))
    f (enode (inj₂ w)) = ind I (bnode (inj₂ (enode w)))

    Iˡ₁⊨F₁ : up * left * bnodes I f ⊨a impl F₁
    Iˡ₁⊨F₁ = ⊨a-resp-≡³ 
      (left * up * I) (on-bnode f (ind I) ∘ left ∘ up) refl (impl F₁) 
      (compose-left F₁ G₁ (up * I) (tensor-up (F₁ ∙ G₁) (F₂ ∙ G₂) I I⊨LHS))

    Iˡ₂⊨F₂ : down * (left * bnodes I f) ⊨a impl F₂
    Iˡ₂⊨F₂ = ⊨a-resp-≡³ 
      (left * down * I) (on-bnode f (ind I) ∘ left ∘ down) refl (impl F₂)
      (compose-left F₂ G₂ (down * I) (tensor-down (F₁ ∙ G₁) (F₂ ∙ G₂) I I⊨LHS))

    Iʳ₁⊨G₁ : up * (right * bnodes I f) ⊨a impl G₁
    Iʳ₁⊨G₁ = ⊨a-resp-≡³
      (right * up * I) (on-bnode f (ind I) ∘ right ∘ up) refl (impl G₁) 
      (compose-right F₁ G₁ (up * I) (tensor-up (F₁ ∙ G₁) (F₂ ∙ G₂) I I⊨LHS))

    Iʳ₂⊨G₂ : down * (right * bnodes I f) ⊨a impl G₂
    Iʳ₂⊨G₂ = ⊨a-resp-≡³
      (right * down * I) (on-bnode f (ind I) ∘ right ∘ down) refl (impl G₂) 
      (compose-right F₂ G₂ (down * I) (tensor-down (F₁ ∙ G₁) (F₂ ∙ G₂) I I⊨LHS))

    I⊨RHS : bnodes I f ⊨a impl ((F₁ ⟨⊗⟩ F₂) ∙ (G₁ ⟨⊗⟩ G₂))
    I⊨RHS = compose-resp-⊨a (F₁ ⟨⊗⟩ F₂) (G₁ ⟨⊗⟩ G₂) (bnodes I f) 
      (tensor-resp-⊨a F₁ F₂ (left * bnodes I f) Iˡ₁⊨F₁ Iˡ₂⊨F₂) 
      (tensor-resp-⊨a G₁ G₂ (right * bnodes I f) Iʳ₁⊨G₁ Iʳ₂⊨G₂) 

  RHS⊑LHS : (F₁ ⟨⊗⟩ F₂) ∙ (G₁ ⟨⊗⟩ G₂) ⊑ (F₁ ∙ G₁) ⟨⊗⟩ (F₂ ∙ G₂)
  RHS⊑LHS I I⊨STA₁A₂ I⊨RHS = (f , I⊨LHS) where

    f : ((BN F₁ ⊕ IN B₁ ⊕ BN G₁) ⊎ (BN F₂ ⊕ IN B₂ ⊕ BN G₂)) → Δ ⌊ I ⌋
    f (inj₁ (inode v)) = ind I (bnode (inode (inj₁ v)))
    f (inj₁ (bnode y)) = ind I (bnode (bnode (inj₁ y)))
    f (inj₁ (enode w)) = ind I (bnode (enode (inj₁ w)))
    f (inj₂ (inode v)) = ind I (bnode (inode (inj₂ v)))
    f (inj₂ (bnode y)) = ind I (bnode (bnode (inj₂ y)))
    f (inj₂ (enode w)) = ind I (bnode (enode (inj₂ w)))

    I₁ˡ⊨F₁ : left * up * bnodes I f ⊨a impl F₁
    I₁ˡ⊨F₁ = ⊨a-resp-≡³
      (up * left * I) (on-bnode f (ind I) ∘ up ∘ left) refl (impl F₁)
      (tensor-up F₁ F₂ (left * I) (compose-left (F₁ ⟨⊗⟩ F₂) (G₁ ⟨⊗⟩ G₂) I I⊨RHS))

    I₁ʳ⊨G₁ : right * up * bnodes I f ⊨a impl G₁
    I₁ʳ⊨G₁ = ⊨a-resp-≡³
      (up * right * I) (on-bnode f (ind I) ∘ up ∘ right) refl (impl G₁)
      (tensor-up G₁ G₂ (right * I) (compose-right (F₁ ⟨⊗⟩ F₂) (G₁ ⟨⊗⟩ G₂) I I⊨RHS))

    I₂ˡ⊨F₂ : left * down * bnodes I f ⊨a impl F₂
    I₂ˡ⊨F₂ = ⊨a-resp-≡³
      (down * left * I) (on-bnode f (ind I) ∘ down ∘ left) refl (impl F₂)
      (tensor-down F₁ F₂ (left * I) (compose-left (F₁ ⟨⊗⟩ F₂) (G₁ ⟨⊗⟩ G₂) I I⊨RHS))

    I₂ʳ⊨G₂ : right * down * bnodes I f ⊨a impl G₂
    I₂ʳ⊨G₂ = ⊨a-resp-≡³
      (down * right * I) (on-bnode f (ind I) ∘ down ∘ right) refl (impl G₂)
      (tensor-down G₁ G₂ (right * I) (compose-right (F₁ ⟨⊗⟩ F₂) (G₁ ⟨⊗⟩ G₂) I I⊨RHS))
    
    I⊨LHS : bnodes I f ⊨a impl ((F₁ ∙ G₁) ⟨⊗⟩ (F₂ ∙ G₂))
    I⊨LHS = tensor-resp-⊨a (F₁ ∙ G₁) (F₂ ∙ G₂) (bnodes I f) 
      (compose-resp-⊨a F₁ G₁ (up * bnodes I f) I₁ˡ⊨F₁ I₁ʳ⊨G₁) 
      (compose-resp-⊨a F₂ G₂ (down * bnodes I f) I₂ˡ⊨F₂ I₂ʳ⊨G₂) 
