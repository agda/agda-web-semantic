open import Relation.Binary.PropositionalEquality using ( refl )
open import Web.Semantic.DL.ABox.Interp using ( _*_ ; ⌊_⌋ ; ind )
open import Web.Semantic.DL.ABox.Interp.Morphism using ( _,_ )
open import Web.Semantic.DL.ABox.Model using
  ( _⊨a_ ; on-bnode ; bnodes ; ⊨a-resp-≲ ; ⊨a-resp-≡³ ; _,_ )
open import Web.Semantic.DL.Category.Object using 
  ( Object ; IN ; iface )
open import Web.Semantic.DL.Category.Morphism using
  ( _⇒_ ; BN ; impl ; _≣_ ; _⊑_ ; _,_ )
open import Web.Semantic.DL.Category.Composition using ( _∙_ )
open import Web.Semantic.DL.Category.Wiring using ( identity )
open import Web.Semantic.DL.Category.Properties.Composition.Lemmas using
  ( compose-left ; compose-right ; compose-resp-⊨a 
  ; identity-intro ; identity-elim )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.DL.TBox.Interp using ( Δ ; _⊨_≈_ ; ≈-refl ; ≈-sym )
open import Web.Semantic.DL.TBox.Interp.Morphism using ( ≲-refl )
open import Web.Semantic.Util using
  ( _∘_ ; _⊕_⊕_ ; False ; inode ; bnode ; enode ; left ; right )

module Web.Semantic.DL.Category.Properties.Composition.LeftUnit
  {Σ : Signature} {S T : TBox Σ} where

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
    I⊨F = ⊨a-resp-≲ (≲-refl ⌊ I ⌋ , f✓) (impl F) Iʳ⊨F

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
