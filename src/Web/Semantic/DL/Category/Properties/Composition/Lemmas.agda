open import Data.Product using ( _,_ ; proj₁ ; proj₂ )
open import Web.Semantic.DL.ABox.Interp using
  ( Interp ; _*_ ; ⌊_⌋ ; ind )
open import Web.Semantic.DL.ABox.Interp.Morphism using
  ( _≲_ ; _**_ ; ≲-refl )
open import Web.Semantic.DL.ABox.Model using
  ( _⊨a_ ; _⊨b_ ; *-resp-⟨ABox⟩ ; ⊨a-resp-≲ )
open import Web.Semantic.DL.Category.Object using
  ( Object ; IN ; fin ; iface )
open import Web.Semantic.DL.Category.Morphism using 
  ( _⇒_ ; _,_ ; BN ; impl
  ; apply ; apply✓ ; apply-init )
open import Web.Semantic.DL.Category.Wiring using
  ( identity ; wires-≈ ; wires-≈⁻¹ )
open import Web.Semantic.DL.Category.Composition using
  ( _∙_ ; ⊨a-intro-⟫ ; ⊨b-intro-⟫ )
open import Web.Semantic.DL.Integrity using ( med-≲ ; init-med )
open import Web.Semantic.DL.KB using ( _,_ )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox ; _,_ )
open import Web.Semantic.DL.TBox.Interp using ( _⊨_≈_ )
open import Web.Semantic.Util using
  ( id ; _⊕_⊕_ ; inode ; bnode ; enode ; left ; right )

module Web.Semantic.DL.Category.Properties.Composition.Lemmas
  {Σ : Signature} {S T : TBox Σ} where

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
