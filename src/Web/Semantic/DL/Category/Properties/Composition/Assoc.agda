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
open import Web.Semantic.DL.Category.Properties.Composition.Lemmas using
  ( compose-left ; compose-right ; compose-resp-⊨a )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.DL.TBox.Interp using ( Δ ; _⊨_≈_ ; ≈-refl ; ≈-sym )
open import Web.Semantic.DL.TBox.Interp.Morphism using ( ≲-refl )
open import Web.Semantic.Util using
  ( _∘_ ; _⊕_⊕_ ; False ; inode ; bnode ; enode ; left ; right )

module Web.Semantic.DL.Category.Properties.Composition.Assoc
  {Σ : Signature} {S T : TBox Σ} where

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

