open import Data.Product using ( _,_ ; proj₁ ; proj₂ )
open import Web.Semantic.DL.ABox.Interp using ( Interp ; _*_ ; ⌊_⌋ ; ind )
open import Web.Semantic.DL.ABox.Interp.Morphism using 
  ( _≲_ ; _,_ ; _**_ ; ≲-refl )
open import Web.Semantic.DL.ABox.Model using 
  ( _⊨a_ ; ⊨a-resp-≲ ; *-resp-⟨ABox⟩ 
  ; _⊨b_ ; ⊨b-resp-≲ ; _,_ ; on-bnode ; bnodes )
open import Web.Semantic.DL.Category.Object using 
  ( Object ; IN ; iface ; fin )
open import Web.Semantic.DL.Category.Morphism using 
  ( _⇒_ ; BN ; impl ; apply ; apply✓ ; apply-init 
  ; _≣_ ; _⊑_ ; _,_ )
open import Web.Semantic.DL.Category.Composition using
  ( compose ; pipe ; pipe-left ; pipe-right ; _⟫_ ; ⊨a-intro-⟫ ; ⊨b-intro-⟫ )
open import Web.Semantic.DL.Category.Identity using
  ( identity ; wire-≈ ; wire-≈⁻¹ )
open import Web.Semantic.DL.Integrity using ( med-≲ ; init-med )
open import Web.Semantic.DL.KB using ( _,_ )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox ; _,_ )
open import Web.Semantic.DL.TBox.Interp using ( Δ ; _⊨_≈_ ; ≈-refl ; ≈-sym )
open import Web.Semantic.DL.TBox.Interp.Morphism using () renaming
  ( ≲-refl to ≲′-refl )
open import Web.Semantic.Util using
  ( False ; _⊕_⊕_ ; inode ; bnode ; enode ; left ; right )

module Web.Semantic.DL.Category.Properties {Σ : Signature} {S T : TBox Σ} where

identity-elim : ∀ (A : Object S T) I → (I ⊨a impl (identity A)) →
  ∀ x → (⌊ I ⌋ ⊨ ind I (inode x) ≈ ind I (enode x))
identity-elim A I I⊨id x = wire-≈ (proj₂ (fin A) x) I⊨id

identity-intro : ∀ (A : Object S T) I → 
  (∀ x → (⌊ I ⌋ ⊨ ind I (inode x) ≈ ind I (enode x))) →
    (I ⊨a impl (identity A))
identity-intro A I ∀x∙x₁≈x₂ = wire-≈⁻¹ ∀x∙x₁≈x₂ (proj₁ (fin A))

compose-left : ∀ {A B C : Object S T} (F : A ⇒ B) (G : B ⇒ C) I →
  (I ⊨a impl (compose F G)) → (left * I ⊨a impl F)
compose-left F G I (I⊨F , I⊨G) = *-resp-⟨ABox⟩ left I (impl F) I⊨F

compose-right : ∀ {A B C : Object S T} (F : A ⇒ B) (G : B ⇒ C) I →
  (I ⊨a impl (compose F G)) → (right * I ⊨a impl G)
compose-right F G I (I⊨F , I⊨G) = *-resp-⟨ABox⟩ right I (impl G) I⊨G

compose-mid : ∀ {A B C : Object S T} (F : A ⇒ B) (G : B ⇒ C) 
  (I : Interp Σ (IN A ⊕ (BN F ⊕ IN B ⊕ BN G) ⊕ IN C)) →
    (inode * I ⊨ (S , T) , iface A) → (I ⊨a impl (compose F G)) →
      (bnode * bnode * I ⊨ (S , T) , iface B)
compose-mid {A} {B} {C} F G I ((I⊨S , I⊨T) , I⊨A) I⊨F⟫G = 
  ((I⊨S , I⊨T) , ⊨a-resp-≲ (enode ** J≲I) (iface B) J⊨B) where

  J : Interp Σ (IN A ⊕ BN F ⊕ IN B)
  J = apply F (inode * I) ((I⊨S , I⊨T) , I⊨A)

  J⊨B : enode * J ⊨a iface B
  J⊨B = proj₂ (apply✓ F (inode * I) ((I⊨S , I⊨T) , I⊨A))

  J≲I : J ≲ left * I
  J≲I = med-≲ (init-med (apply-init F (inode * I) ((I⊨S , I⊨T) , I⊨A)) 
    (left * I) (≲-refl (inode * I)) (I⊨S , compose-left F G I I⊨F⟫G))

compose-resp-⊨a : ∀ {A B C : Object S T} (F : A ⇒ B) (G : B ⇒ C) I →
  (left * I ⊨a impl F) → (right * I ⊨a impl G) → (I ⊨a impl (compose F G))
compose-resp-⊨a F G I I⊨F I⊨G = ⊨a-intro-⟫ I (impl F) (impl G) I⊨F I⊨G

compose-resp-⊨b : ∀ {V W} {A B C : Object S T} (F : A ⇒ B) (G : B ⇒ C) 
  (I : Interp Σ (IN A ⊕ (V ⊕ IN B ⊕ W) ⊕ IN C)) →
    (left * I ⊨b impl F) → (right * I ⊨b impl G) → (I ⊨b impl (compose F G))
compose-resp-⊨b F G I I⊨F I⊨G = ⊨b-intro-⟫ I (impl F) (impl G) I⊨F I⊨G

compose-resp-⊑ : ∀ {A B C : Object S T} (F₁ F₂ : A ⇒ B) (G₁ G₂ : B ⇒ C) → 
  (F₁ ⊑ F₂) → (G₁ ⊑ G₂) → (compose F₁ G₁ ⊑ compose F₂ G₂)
compose-resp-⊑ F₁ F₂ G₁ G₂ F₁⊑F₂ G₁⊑G₂ I I⊨STA I⊨F₁⟫G₁ = 
  compose-resp-⊨b F₂ G₂ I 
    (F₁⊑F₂ (left * I) I⊨STA 
      (compose-left F₁ G₁ I I⊨F₁⟫G₁)) 
    (G₁⊑G₂ (right * I) (compose-mid F₁ G₁ I I⊨STA I⊨F₁⟫G₁)
      (compose-right F₁ G₁ I I⊨F₁⟫G₁))

compose-resp-≣ : ∀ {A B C : Object S T} (F₁ F₂ : A ⇒ B) (G₁ G₂ : B ⇒ C) → 
  (F₁ ≣ F₂) → (G₁ ≣ G₂) → (compose F₁ G₁ ≣ compose F₂ G₂)
compose-resp-≣ F₁ F₂ G₁ G₂ (F₁⊑F₂ , F₂⊑F₁) (G₁⊑G₂ , G₂⊑G₁) = 
  ( compose-resp-⊑ F₁ F₂ G₁ G₂ F₁⊑F₂ G₁⊑G₂ 
  , compose-resp-⊑ F₂ F₁ G₂ G₁ F₂⊑F₁ G₂⊑G₁ )

compose-unit₁ : ∀ {A B : Object S T} (F : A ⇒ B) → 
  (compose (identity A) F ≣ F)
compose-unit₁ {A} {B} F = ( idF⊑F , F⊑idF ) where

  idF⊑F : compose (identity A) F ⊑ F
  idF⊑F I I⊨STA I⊨idF = (f , I⊨F) where

    Iˡ⊨id : left * I ⊨a impl (identity A)
    Iˡ⊨id = compose-left (identity A) F I I⊨idF

    Iʳ⊨F : right * I ⊨a impl F
    Iʳ⊨F = compose-right (identity A) F I I⊨idF

    f : BN F → Δ ⌊ I ⌋
    f w = ind I (bnode (enode w))

    f✓ : ∀ x → ⌊ I ⌋ ⊨ ind I (right x) ≈ on-bnode f (ind I) x
    f✓ (inode x) = ≈-sym ⌊ I ⌋ (identity-elim A (left * I) Iˡ⊨id x)
    f✓ (bnode v) = ≈-refl ⌊ I ⌋
    f✓ (enode y) = ≈-refl ⌊ I ⌋

    I⊨F : bnodes I f ⊨a impl F
    I⊨F = ⊨a-resp-≲ (≲′-refl ⌊ I ⌋ , f✓) (impl F) Iʳ⊨F

  F⊑idF : F ⊑ compose (identity A) F
  F⊑idF I I⊨STA I⊨F = (f , I⊨idF) where

    f : (False ⊕ IN A ⊕ BN F) → Δ ⌊ I ⌋
    f (inode ())
    f (bnode x) = ind I (inode x)
    f (enode v) = ind I (bnode v)

    f✓ : ∀ x → ⌊ I ⌋ ⊨ ind I x ≈ on-bnode f (ind I) (right x)
    f✓ (inode x) = ≈-refl ⌊ I ⌋
    f✓ (bnode v) = ≈-refl ⌊ I ⌋
    f✓ (enode y) = ≈-refl ⌊ I ⌋

    Iˡ⊨I : left * bnodes I f ⊨a impl (identity A)
    Iˡ⊨I = identity-intro A (left * bnodes I f) (λ x → ≈-refl ⌊ I ⌋)

    Iʳ⊨F : right * bnodes I f ⊨a impl F
    Iʳ⊨F = ⊨a-resp-≲ (≲′-refl ⌊ I ⌋ , f✓) (impl F) I⊨F

    I⊨idF : bnodes I f ⊨a impl (compose (identity A) F)
    I⊨idF = compose-resp-⊨a (identity A) F (bnodes I f) Iˡ⊨I Iʳ⊨F
