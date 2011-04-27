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

module Web.Semantic.DL.Category.Properties.Composition.RightUnit
  {Σ : Signature} {S T : TBox Σ} where

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
    I⊨F = ⊨a-resp-≲ (≲-refl ⌊ I ⌋ , f✓) (impl F) Iˡ⊨F

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
