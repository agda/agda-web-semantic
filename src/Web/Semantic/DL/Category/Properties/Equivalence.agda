open import Relation.Binary.PropositionalEquality using ( refl )
open import Web.Semantic.DL.ABox.Interp using ( Interp ; ⌊_⌋ ; ind ; _*_ )
open import Web.Semantic.DL.ABox.Model using
  ( _⊨a_ ; ⊨a-resp-≡³ ; ⊨a-impl-⊨b ; ⊨b-impl-⊨a
  ; _,_ ; inb ; on-bnode ; bnodes )
open import Web.Semantic.DL.Category.Object using ( Object ; IN ; iface )
open import Web.Semantic.DL.Category.Morphism using
  ( _⇒_ ; _,_ ; BN ; impl ; _⊑_ ; _≣_ )
open import Web.Semantic.DL.KB using ( _,_ )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox ; _,_ )
open import Web.Semantic.DL.TBox.Interp using ( Δ )
open import Web.Semantic.Util using ( _⊕_⊕_ ; inode )

module Web.Semantic.DL.Category.Properties.Equivalence 
  {Σ : Signature} {S T : TBox Σ} where

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
