open import Data.Product using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; cong )
open import Web.Semantic.DL.ABox.Interp using 
  ( Interp ; _,_ ; _*_ ; ⌊_⌋ ; ind )
open import Web.Semantic.DL.ABox.Interp.Morphism using 
  ( _≲_ ; _,_ ; _**_ ; ≲-refl )
open import Web.Semantic.DL.ABox.Model using 
  ( _⊨a_ ; ⊨a-resp-≲ ; ⊨a-impl-⊨b ; *-resp-⟨ABox⟩ ; ⊨a-resp-≡³
  ; _⊨b_ ; ⊨b-resp-≲ ; ⊨b-impl-⊨a ; _,_ ; inb ; on-bnode ; bnodes )
open import Web.Semantic.DL.Category.Object using 
  ( Object ; IN ; iface ; fin )
open import Web.Semantic.DL.Category.Morphism using 
  ( _⇒_ ; BN ; impl ; apply ; apply✓ ; apply-init 
  ; _≣_ ; _⊑_ ; _,_ )
open import Web.Semantic.DL.Category.Composition using
  ( _∙_ ; pipe ; pipe-left ; pipe-right ; _⟫_ ; ⊨a-intro-⟫ ; ⊨b-intro-⟫ )
open import Web.Semantic.DL.Category.Wiring using
  ( identity ; wires-≈ ; wires-≈⁻¹ )
open import Web.Semantic.DL.Integrity using ( med-≲ ; init-med )
open import Web.Semantic.DL.KB using ( _,_ )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox ; _,_ )
open import Web.Semantic.DL.TBox.Interp using 
  ( Δ ; _⊨_≈_ ; ≈-refl ; ≈-sym ) renaming
  ( Interp to Interp′ )
open import Web.Semantic.DL.TBox.Interp.Morphism using () renaming
  ( ≲-refl to ≲′-refl )
open import Web.Semantic.Util using
  ( id ; _∘_ ; False ; _⊕_⊕_ ; inode ; bnode ; enode ; left ; right )

module Web.Semantic.DL.Category.IsCategory {Σ : Signature} {S T : TBox Σ} where

⊑-refl : ∀ {A B : Object S T} (F : A ⇒ B) → (F ⊑ F)
⊑-refl F I I⊨STA I⊨F = ⊨a-impl-⊨b I (impl F) I⊨F

⊑-trans : ∀ {A B : Object S T} (F G H : A ⇒ B) → (F ⊑ G) → (G ⊑ H) → (F ⊑ H)
⊑-trans {A} {B} F G H F⊑G G⊑H I I⊨STA I⊨F = (g , I⊨H) where

  f : BN G → Δ ⌊ I ⌋
  f = inb (F⊑G I I⊨STA I⊨F)

  J : Interp Σ (IN A ⊕ BN G ⊕ IN B)
  J = bnodes I f

  J⊨STA : inode * J ⊨ (S , T) , iface A
  J⊨STA = I⊨STA

  J⊨G : J ⊨a impl G
  J⊨G = ⊨b-impl-⊨a (F⊑G I I⊨STA I⊨F)
  
  g : BN H → Δ ⌊ I ⌋
  g = inb (G⊑H J J⊨STA J⊨G)

  K : Interp Σ (IN A ⊕ BN H ⊕ IN B)
  K = bnodes J g

  K⊨H : K ⊨a impl H
  K⊨H = ⊨b-impl-⊨a (G⊑H J J⊨STA J⊨G)

  I⊨H : bnodes I g ⊨a impl H
  I⊨H = ⊨a-resp-≡³ K (on-bnode g (ind I)) refl (impl H) K⊨H

≣-refl : ∀ {A B : Object S T} (F : A ⇒ B) → (F ≣ F)
≣-refl F = (⊑-refl F , ⊑-refl F)

≣-sym :  ∀ {A B : Object S T} {F G : A ⇒ B} → (F ≣ G) → (G ≣ F)
≣-sym (F⊑G , G⊑F) = (G⊑F , F⊑G)

≣-trans :  ∀ {A B : Object S T} {F G H : A ⇒ B} → (F ≣ G) → (G ≣ H) → (F ≣ H)
≣-trans {A} {B} {F} {G} {H} (F⊑G , G⊑F) (G⊑H , H⊑G) = 
  (⊑-trans F G H F⊑G G⊑H , ⊑-trans H G F H⊑G G⊑F)

identity-elim : ∀ (A : Object S T) I → (I ⊨a impl (identity A)) →
  ∀ x → (⌊ I ⌋ ⊨ ind I (inode x) ≈ ind I (enode x))
identity-elim A I I⊨id x = wires-≈ id (proj₂ (fin A) x) I⊨id

identity-intro : ∀ (A : Object S T) I → 
  (∀ x → (⌊ I ⌋ ⊨ ind I (inode x) ≈ ind I (enode x))) →
    (I ⊨a impl (identity A))
identity-intro A I ∀x∙x₁≈x₂ = wires-≈⁻¹ id ∀x∙x₁≈x₂ (proj₁ (fin A))

compose-left : ∀ {A B C : Object S T} (F : A ⇒ B) (G : B ⇒ C) I →
  (I ⊨a impl (F ∙ G)) → (left * I ⊨a impl F)
compose-left F G I (I⊨F , I⊨G) = *-resp-⟨ABox⟩ left I (impl F) I⊨F

compose-right : ∀ {A B C : Object S T} (F : A ⇒ B) (G : B ⇒ C) I →
  (I ⊨a impl (F ∙ G)) → (right * I ⊨a impl G)
compose-right F G I (I⊨F , I⊨G) = *-resp-⟨ABox⟩ right I (impl G) I⊨G

compose-mid : ∀ {A B C : Object S T} (F : A ⇒ B) (G : B ⇒ C) 
  (I : Interp Σ (IN A ⊕ (BN F ⊕ IN B ⊕ BN G) ⊕ IN C)) →
    (inode * I ⊨ (S , T) , iface A) → (I ⊨a impl (F ∙ G)) →
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
  (left * I ⊨a impl F) → (right * I ⊨a impl G) → (I ⊨a impl (F ∙ G))
compose-resp-⊨a F G I I⊨F I⊨G = ⊨a-intro-⟫ I (impl F) (impl G) I⊨F I⊨G

compose-resp-⊨b : ∀ {V W} {A B C : Object S T} (F : A ⇒ B) (G : B ⇒ C) 
  (I : Interp Σ (IN A ⊕ (V ⊕ IN B ⊕ W) ⊕ IN C)) →
    (left * I ⊨b impl F) → (right * I ⊨b impl G) → (I ⊨b impl (F ∙ G))
compose-resp-⊨b F G I I⊨F I⊨G = ⊨b-intro-⟫ I (impl F) (impl G) I⊨F I⊨G

compose-resp-⊑ : ∀ {A B C : Object S T} (F₁ F₂ : A ⇒ B) (G₁ G₂ : B ⇒ C) → 
  (F₁ ⊑ F₂) → (G₁ ⊑ G₂) → (F₁ ∙ G₁ ⊑ F₂ ∙ G₂)
compose-resp-⊑ F₁ F₂ G₁ G₂ F₁⊑F₂ G₁⊑G₂ I I⊨STA I⊨F₁⟫G₁ = 
  compose-resp-⊨b F₂ G₂ I 
    (F₁⊑F₂ (left * I) I⊨STA 
      (compose-left F₁ G₁ I I⊨F₁⟫G₁)) 
    (G₁⊑G₂ (right * I) (compose-mid F₁ G₁ I I⊨STA I⊨F₁⟫G₁)
      (compose-right F₁ G₁ I I⊨F₁⟫G₁))

compose-resp-≣ : ∀ {A B C : Object S T} (F₁ F₂ : A ⇒ B) (G₁ G₂ : B ⇒ C) → 
  (F₁ ≣ F₂) → (G₁ ≣ G₂) → (F₁ ∙ G₁ ≣ F₂ ∙ G₂)
compose-resp-≣ F₁ F₂ G₁ G₂ (F₁⊑F₂ , F₂⊑F₁) (G₁⊑G₂ , G₂⊑G₁) = 
  ( compose-resp-⊑ F₁ F₂ G₁ G₂ F₁⊑F₂ G₁⊑G₂ 
  , compose-resp-⊑ F₂ F₁ G₂ G₁ F₂⊑F₁ G₂⊑G₁ )

compose-unit₁ : ∀ {A B : Object S T} (F : A ⇒ B) → 
  (identity A ∙ F ≣ F)
compose-unit₁ {A} {B} F = ( idF⊑F , F⊑idF ) where

  idF⊑F : identity A ∙ F ⊑ F
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

  F⊑idF : F ⊑ identity A ∙ F
  F⊑idF I I⊨STA I⊨F = (f , I⊨idF) where

    f : (False ⊕ IN A ⊕ BN F) → Δ ⌊ I ⌋
    f (inode ())
    f (bnode x) = ind I (inode x)
    f (enode v) = ind I (bnode v)

    Iˡ⊨id : left * bnodes I f ⊨a impl (identity A)
    Iˡ⊨id = identity-intro A (left * bnodes I f) (λ x → ≈-refl ⌊ I ⌋)

    Iʳ⊨F : right * bnodes I f ⊨a impl F
    Iʳ⊨F = ⊨a-resp-≡³ I (on-bnode f (ind I) ∘ right) refl (impl F) I⊨F

    I⊨idF : bnodes I f ⊨a impl (identity A ∙ F)
    I⊨idF = compose-resp-⊨a (identity A) F (bnodes I f) Iˡ⊨id Iʳ⊨F

compose-unit₂ : ∀ {A B : Object S T} (F : A ⇒ B) → 
  (F ∙ identity B ≣ F)
compose-unit₂ {A} {B} F = ( Fid⊑F , F⊑Fid ) where

  Fid⊑F : F ∙ identity B ⊑ F
  Fid⊑F I I⊨STA I⊨Fid = (f , I⊨F) where

    Iˡ⊨F : left * I ⊨a impl F
    Iˡ⊨F = compose-left F (identity B) I I⊨Fid

    Iʳ⊨id : right * I ⊨a impl (identity B)
    Iʳ⊨id = compose-right F (identity B) I I⊨Fid

    f : BN F → Δ ⌊ I ⌋
    f w = ind I (bnode (inode w))

    f✓ : ∀ x → ⌊ I ⌋ ⊨ ind I (left x) ≈ on-bnode f (ind I) x
    f✓ (inode x) = ≈-refl ⌊ I ⌋
    f✓ (bnode v) = ≈-refl ⌊ I ⌋
    f✓ (enode y) = identity-elim B (right * I) Iʳ⊨id y

    I⊨F : bnodes I f ⊨a impl F
    I⊨F = ⊨a-resp-≲ (≲′-refl ⌊ I ⌋ , f✓) (impl F) Iˡ⊨F

  F⊑Fid : F ⊑ F ∙ identity B
  F⊑Fid I I⊨STA I⊨F = (f , I⊨Fid) where

    f : (BN F ⊕ IN B ⊕ False) → Δ ⌊ I ⌋
    f (inode v) = ind I (bnode v)
    f (bnode y) = ind I (enode y)
    f (enode ())

    Iˡ⊨F : left * bnodes I f ⊨a impl F
    Iˡ⊨F = ⊨a-resp-≡³ I (on-bnode f (ind I) ∘ left) refl (impl F) I⊨F

    Iʳ⊨id : right * bnodes I f ⊨a impl (identity B)
    Iʳ⊨id = identity-intro B (right * bnodes I f) (λ x → ≈-refl ⌊ I ⌋)

    I⊨Fid : bnodes I f ⊨a impl (F ∙ identity B)
    I⊨Fid = compose-resp-⊨a F (identity B) (bnodes I f) Iˡ⊨F Iʳ⊨id

compose-assoc : ∀ {A B C D : Object S T} (F : A ⇒ B) (G : B ⇒ C) (H : C ⇒ D) →
  ((F ∙ G) ∙ H ≣ F ∙ (G ∙ H))
compose-assoc {A} {B} {C} {D} F G H = (LHS⊑RHS , RHS⊑LHS) where

  LHS⊑RHS : (F ∙ G) ∙ H ⊑ F ∙ (G ∙ H)
  LHS⊑RHS I I⊨STA I⊨LHS = (f , I⊨RHS) where

    f : (BN F ⊕ IN B ⊕ (BN G ⊕ IN C ⊕ BN H)) → Δ ⌊ I ⌋
    f (inode u) = ind I (bnode (inode (inode u)))
    f (bnode y) = ind I (bnode (inode (bnode y)))
    f (enode (inode v)) = ind I (bnode (inode (enode v)))
    f (enode (bnode z)) = ind I (bnode (bnode z))
    f (enode (enode w)) = ind I (bnode (enode w))

    I⊨F : left * bnodes I f ⊨a impl F
    I⊨F = ⊨a-resp-≡³ (left * left * I) (on-bnode f (ind I) ∘ left) refl 
      (impl F) (compose-left F G (left * I) (compose-left (F ∙ G) H I I⊨LHS))

    I⊨G : left * right * bnodes I f ⊨a impl G
    I⊨G = ⊨a-resp-≡³ (right * left * I) (on-bnode f (ind I) ∘ right ∘ left) refl
      (impl G) (compose-right F G (left * I) (compose-left (F ∙ G) H I I⊨LHS))

    I⊨H : right * right * bnodes I f ⊨a impl H
    I⊨H = ⊨a-resp-≡³ (right * I) (on-bnode f (ind I) ∘ right ∘ right) refl
      (impl H) (compose-right (F ∙ G) H I I⊨LHS)

    I⊨RHS : bnodes I f ⊨a impl (F ∙ (G ∙ H))
    I⊨RHS = compose-resp-⊨a F (G ∙ H) (bnodes I f) I⊨F 
      (compose-resp-⊨a G H (right * bnodes I f) I⊨G I⊨H)

  RHS⊑LHS : F ∙ (G ∙ H) ⊑ (F ∙ G) ∙ H
  RHS⊑LHS I I⊨STA I⊨RHS = (f , I⊨LHS) where

    f : ((BN F ⊕ IN B ⊕ BN G) ⊕ IN C ⊕ BN H) → Δ ⌊ I ⌋
    f (inode (inode u)) = ind I (bnode (inode u))
    f (inode (bnode y)) = ind I (bnode (bnode y))
    f (inode (enode v)) = ind I (bnode (enode (inode v)))
    f (bnode z) = ind I (bnode (enode (bnode z)))
    f (enode w) = ind I (bnode (enode (enode w)))

    I⊨F : left * left * bnodes I f ⊨a impl F
    I⊨F = ⊨a-resp-≡³ (left * I) (on-bnode f (ind I) ∘ left ∘ left) refl
      (impl F) (compose-left F (G ∙ H) I I⊨RHS)

    I⊨G : right * left * bnodes I f ⊨a impl G
    I⊨G = ⊨a-resp-≡³ (left * right * I) (on-bnode f (ind I) ∘ left ∘ right) refl
      (impl G) (compose-left G H (right * I) (compose-right F (G ∙ H) I I⊨RHS))

    I⊨H : right * bnodes I f ⊨a impl H
    I⊨H = ⊨a-resp-≡³ (right * right * I) (on-bnode f (ind I) ∘ right) refl
      (impl H) (compose-right G H (right * I) (compose-right F (G ∙ H) I I⊨RHS))

    I⊨LHS : bnodes I f ⊨a impl ((F ∙ G) ∙ H)
    I⊨LHS = compose-resp-⊨a (F ∙ G) H (bnodes I f) 
      (compose-resp-⊨a F G (left * bnodes I f) I⊨F I⊨G) I⊨H

