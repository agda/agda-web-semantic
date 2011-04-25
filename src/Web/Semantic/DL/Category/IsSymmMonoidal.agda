open import Data.Product using ( _,_ )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Web.Semantic.DL.ABox using ( ABox )
open import Web.Semantic.DL.ABox.Interp using ( Interp ; _,_ ; ⌊_⌋ ; ind ; _*_ )
open import Web.Semantic.DL.ABox.Interp.Morphism using ( ≡³-impl-≈ )
open import Web.Semantic.DL.ABox.Model using ( _⊨a_ ; _⊨b_ ; _,_ ; bnodes ; on-bnode ; *-resp-⟨ABox⟩ ; ⟨ABox⟩-resp-⊨ ; ⊨a-resp-≡³ )
open import Web.Semantic.DL.Category.IsCategory using ( compose-resp-⊨a ; compose-left ; compose-right )
open import Web.Semantic.DL.Category.Object using 
  ( Object ; IN ; iface ; fin )
open import Web.Semantic.DL.Category.Morphism using 
  ( _⇒_ ; BN ; impl ; apply ; apply✓ ; apply-init 
  ; _≣_ ; _⊑_ ; _,_ )
open import Web.Semantic.DL.Category.Composition using ( _∙_ )
open import Web.Semantic.DL.Category.Tensor using ( _&_ ; _⟨&⟩_ ; _⊗_ ; _⟨⊗⟩_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.DL.TBox.Interp using ( Δ ; ≈-refl )
open import Web.Semantic.Util using ( _∘_ ; _⊕_⊕_ ; inode ; bnode ; enode ; left ; right ; ⊕-inj₁ ; ⊕-inj₂ )

module Web.Semantic.DL.Category.IsSymmMonoidal {Σ : Signature} {S T : TBox Σ} where

obj₁ : ∀ (A₁ A₂ : Object S T) I → (I ⊨a iface (A₁ ⊗ A₂)) → (inj₁ * I ⊨a iface A₁)
obj₁ A₁ A₂ I (I⊨A₁ , I⊨A₂) = *-resp-⟨ABox⟩ inj₁ I (iface A₁) I⊨A₁

obj₂ : ∀ (A₁ A₂ : Object S T) I → (I ⊨a iface (A₁ ⊗ A₂)) → (inj₂ * I ⊨a iface A₂)
obj₂ A₁ A₂ I (I⊨A₁ , I⊨A₂) = *-resp-⟨ABox⟩ inj₂ I (iface A₂) I⊨A₂

morph₁ : ∀ {A₁ A₂ B₁ B₂ : Object S T} (F₁ : A₁ ⇒ B₁) (F₂ : A₂ ⇒ B₂) I → 
  (I ⊨a impl (F₁ ⟨⊗⟩ F₂)) → (⊕-inj₁ * I ⊨a impl F₁)
morph₁ F₁ F₂ I (I⊨F₁ , I⊨F₂) = *-resp-⟨ABox⟩ ⊕-inj₁ I (impl F₁) I⊨F₁

morph₂ : ∀ {A₁ A₂ B₁ B₂ : Object S T} (F₁ : A₁ ⇒ B₁) (F₂ : A₂ ⇒ B₂) I → 
  (I ⊨a impl (F₁ ⟨⊗⟩ F₂)) → (⊕-inj₂ * I ⊨a impl F₂)
morph₂ F₁ F₂ I (I⊨F₁ , I⊨F₂) = *-resp-⟨ABox⟩ ⊕-inj₂ I (impl F₂) I⊨F₂

⊨a-intro-⟨&⟩ : ∀ {V₁ V₂ X₁ X₂ Y₁ Y₂} → (I : Interp Σ ((X₁ ⊎ X₂) ⊕ (V₁ ⊎ V₂) ⊕ (Y₁ ⊎ Y₂))) →
  (F₁ : ABox Σ (X₁ ⊕ V₁ ⊕ Y₁)) → (F₂ : ABox Σ (X₂ ⊕ V₂ ⊕ Y₂)) →
    (⊕-inj₁ * I ⊨a F₁) → (⊕-inj₂ * I ⊨a F₂) → (I ⊨a F₁ ⟨&⟩ F₂)
⊨a-intro-⟨&⟩ (I , i) F₁ F₂ I₁⊨F₁ I₂⊨F₂ = 
  ( ⟨ABox⟩-resp-⊨ ⊕-inj₁ (λ x → ≈-refl I) F₁ I₁⊨F₁
  , ⟨ABox⟩-resp-⊨ ⊕-inj₂ (λ x → ≈-refl I) F₂ I₂⊨F₂ )

⊨b-intro-⟨&⟩ : ∀ {V₁ V₂ W₁ W₂ X₁ X₂ Y₁ Y₂} → (I : Interp Σ ((X₁ ⊎ X₂) ⊕ (W₁ ⊎ W₂) ⊕ (Y₁ ⊎ Y₂))) →
  (F₁ : ABox Σ (X₁ ⊕ V₁ ⊕ Y₁)) → (F₂ : ABox Σ (X₂ ⊕ V₂ ⊕ Y₂)) →
    (⊕-inj₁ * I ⊨b F₁) → (⊕-inj₂ * I ⊨b F₂) → (I ⊨b F₁ ⟨&⟩ F₂)
⊨b-intro-⟨&⟩ {V₁} {V₂} I F₁ F₂ (f₁ , I₁⊨F₁) (f₂ , I₂⊨F₂) = 
  (f , I⊨F₁F₂) where

  f : (V₁ ⊎ V₂) → Δ ⌊ I ⌋
  f (inj₁ v) = f₁ v
  f (inj₂ v) = f₂ v

  I⊨F₁F₂ : bnodes I f ⊨a F₁ ⟨&⟩ F₂
  I⊨F₁F₂ = 
    ( ⟨ABox⟩-resp-⊨ ⊕-inj₁ 
        (≡³-impl-≈ ⌊ I ⌋ (on-bnode f₁ (ind I ∘ ⊕-inj₁)) (on-bnode f (ind I) ∘ ⊕-inj₁) refl) 
        F₁ I₁⊨F₁
    , ⟨ABox⟩-resp-⊨ ⊕-inj₂ 
        (≡³-impl-≈ ⌊ I ⌋ (on-bnode f₂ (ind I ∘ ⊕-inj₂)) (on-bnode f (ind I) ∘ ⊕-inj₂) refl) 
        F₂ I₂⊨F₂ )

tensor-resp-⊨a : ∀ {A₁ A₂ B₁ B₂ : Object S T} (F₁ : A₁ ⇒ B₁) (F₂ : A₂ ⇒ B₂) →
  (I : Interp Σ ((IN A₁ ⊎ IN A₂) ⊕ (BN F₁ ⊎ BN F₂) ⊕ (IN B₁ ⊎ IN B₂))) →
    (⊕-inj₁ * I ⊨a impl F₁) → (⊕-inj₂ * I ⊨a impl F₂) → (I ⊨a impl (F₁ ⟨⊗⟩ F₂))
tensor-resp-⊨a F₁ F₂ I I₁⊨F₁ I₂⊨F₂ = ⊨a-intro-⟨&⟩ I (impl F₁) (impl F₂) I₁⊨F₁ I₂⊨F₂

tensor-resp-⊨b : ∀ {V₁ V₂} {A₁ A₂ B₁ B₂ : Object S T} (F₁ : A₁ ⇒ B₁) (F₂ : A₂ ⇒ B₂) →
  (I : Interp Σ ((IN A₁ ⊎ IN A₂) ⊕ (V₁ ⊎ V₂) ⊕ (IN B₁ ⊎ IN B₂))) →
    (⊕-inj₁ * I ⊨b impl F₁) → (⊕-inj₂ * I ⊨b impl F₂) → (I ⊨b impl (F₁ ⟨⊗⟩ F₂))
tensor-resp-⊨b F₁ F₂ I I⊨F₁ I⊨F₂ = ⊨b-intro-⟨&⟩ I (impl F₁) (impl F₂) I⊨F₁ I⊨F₂

tensor-resp-⊑ : ∀ {A₁ A₂ B₁ B₂ : Object S T} (F₁ G₁ : A₁ ⇒ B₁) (F₂ G₂ : A₂ ⇒ B₂) → 
  (F₁ ⊑ G₁) → (F₂ ⊑ G₂) → (F₁ ⟨⊗⟩ F₂ ⊑ G₁ ⟨⊗⟩ G₂)
tensor-resp-⊑ {A₁} {A₂} F₁ G₁ F₂ G₂ F₁⊑G₁ F₂⊑G₂ I (I⊨ST , I⊨A₁A₂) I⊨F₁F₂ = 
  tensor-resp-⊨b G₁ G₂ I 
    (F₁⊑G₁ (⊕-inj₁ * I) (I⊨ST , obj₁ A₁ A₂ (inode * I) I⊨A₁A₂) (morph₁ F₁ F₂ I I⊨F₁F₂)) 
    (F₂⊑G₂ (⊕-inj₂ * I) (I⊨ST , obj₂ A₁ A₂ (inode * I) I⊨A₁A₂) (morph₂ F₁ F₂ I I⊨F₁F₂)) 

tensor-resp-≣ : ∀ {A₁ A₂ B₁ B₂ : Object S T} (F₁ G₁ : A₁ ⇒ B₁) (F₂ G₂ : A₂ ⇒ B₂) → 
  (F₁ ≣ G₁) → (F₂ ≣ G₂) → (F₁ ⟨⊗⟩ F₂ ≣ G₁ ⟨⊗⟩ G₂)
tensor-resp-≣ F₁ G₁ F₂ G₂ (F₁⊑G₁ , G₁⊑F₁) (F₂⊑G₂ , G₂⊑F₂) = 
  ( tensor-resp-⊑ F₁ G₁ F₂ G₂ F₁⊑G₁ F₂⊑G₂
  , tensor-resp-⊑ G₁ F₁ G₂ F₂ G₁⊑F₁ G₂⊑F₂ )

tensor-dist-compose :  ∀ {A₁ A₂ B₁ B₂ C₁ C₂ : Object S T}
  (F₁ : A₁ ⇒ B₁) (F₂ : A₂ ⇒ B₂) (G₁ : B₁ ⇒ C₁) (G₂ : B₂ ⇒ C₂) →
    (((F₁ ∙ G₁) ⟨⊗⟩ (F₂ ∙ G₂)) ≣ ((F₁ ⟨⊗⟩ F₂) ∙ (G₁ ⟨⊗⟩ G₂)))
tensor-dist-compose {A₁} {A₂} {B₁} {B₂} {C₁} {C₂} F₁ F₂ G₁ G₂ = 
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

    Iˡ₁⊨F₁ : ⊕-inj₁ * left * bnodes I f ⊨a impl F₁
    Iˡ₁⊨F₁ = ⊨a-resp-≡³ (left * ⊕-inj₁ * I) (on-bnode f (ind I) ∘ left ∘ ⊕-inj₁) refl (impl F₁) 
      (compose-left F₁ G₁ (⊕-inj₁ * I) (morph₁ (F₁ ∙ G₁) (F₂ ∙ G₂) I I⊨LHS))

    Iˡ₂⊨F₂ : ⊕-inj₂ * (left * bnodes I f) ⊨a impl F₂
    Iˡ₂⊨F₂ = ⊨a-resp-≡³ (left * ⊕-inj₂ * I) (on-bnode f (ind I) ∘ left ∘ ⊕-inj₂) refl (impl F₂)
      (compose-left F₂ G₂ (⊕-inj₂ * I) (morph₂ (F₁ ∙ G₁) (F₂ ∙ G₂) I I⊨LHS))

    Iʳ₁⊨G₁ : ⊕-inj₁ * (right * bnodes I f) ⊨a impl G₁
    Iʳ₁⊨G₁ = ⊨a-resp-≡³ (right * ⊕-inj₁ * I) (on-bnode f (ind I) ∘ right ∘ ⊕-inj₁) refl (impl G₁) 
      (compose-right F₁ G₁ (⊕-inj₁ * I) (morph₁ (F₁ ∙ G₁) (F₂ ∙ G₂) I I⊨LHS))

    Iʳ₂⊨G₂ : ⊕-inj₂ * (right * bnodes I f) ⊨a impl G₂
    Iʳ₂⊨G₂ = ⊨a-resp-≡³ (right * ⊕-inj₂ * I) (on-bnode f (ind I) ∘ right ∘ ⊕-inj₂) refl (impl G₂) 
      (compose-right F₂ G₂ (⊕-inj₂ * I) (morph₂ (F₁ ∙ G₁) (F₂ ∙ G₂) I I⊨LHS))

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

    I₁ˡ⊨F₁ : left * ⊕-inj₁ * bnodes I f ⊨a impl F₁
    I₁ˡ⊨F₁ = ⊨a-resp-≡³ (⊕-inj₁ * left * I) (on-bnode f (ind I) ∘ ⊕-inj₁ ∘ left) refl (impl F₁)
               (morph₁ F₁ F₂ (left * I) (compose-left (F₁ ⟨⊗⟩ F₂) (G₁ ⟨⊗⟩ G₂) I I⊨RHS))

    I₁ʳ⊨G₁ : right * ⊕-inj₁ * bnodes I f ⊨a impl G₁
    I₁ʳ⊨G₁ = ⊨a-resp-≡³ (⊕-inj₁ * right * I) (on-bnode f (ind I) ∘ ⊕-inj₁ ∘ right) refl (impl G₁)
               (morph₁ G₁ G₂ (right * I) (compose-right (F₁ ⟨⊗⟩ F₂) (G₁ ⟨⊗⟩ G₂) I I⊨RHS))

    I₂ˡ⊨F₂ : left * ⊕-inj₂ * bnodes I f ⊨a impl F₂
    I₂ˡ⊨F₂ = ⊨a-resp-≡³ (⊕-inj₂ * left * I) (on-bnode f (ind I) ∘ ⊕-inj₂ ∘ left) refl (impl F₂)
               (morph₂ F₁ F₂ (left * I) (compose-left (F₁ ⟨⊗⟩ F₂) (G₁ ⟨⊗⟩ G₂) I I⊨RHS))

    I₂ʳ⊨G₂ : right * ⊕-inj₂ * bnodes I f ⊨a impl G₂
    I₂ʳ⊨G₂ = ⊨a-resp-≡³ (⊕-inj₂ * right * I) (on-bnode f (ind I) ∘ ⊕-inj₂ ∘ right) refl (impl G₂)
               (morph₂ G₁ G₂ (right * I) (compose-right (F₁ ⟨⊗⟩ F₂) (G₁ ⟨⊗⟩ G₂) I I⊨RHS))
    
    I⊨LHS : bnodes I f ⊨a impl ((F₁ ∙ G₁) ⟨⊗⟩ (F₂ ∙ G₂))
    I⊨LHS = tensor-resp-⊨a (F₁ ∙ G₁) (F₂ ∙ G₂) (bnodes I f) 
      (compose-resp-⊨a F₁ G₁ (⊕-inj₁ * bnodes I f) I₁ˡ⊨F₁ I₁ʳ⊨G₁) 
      (compose-resp-⊨a F₂ G₂ (⊕-inj₂ * bnodes I f) I₂ˡ⊨F₂ I₂ʳ⊨G₂) 
