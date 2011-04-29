open import Data.List using ( [] )
open import Data.Product using ( proj₁ ; proj₂ )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Web.Semantic.DL.ABox.Interp using ( ⌊_⌋ ; ind ; _*_ )
open import Web.Semantic.DL.ABox.Interp.Morphism using ( _,_ )
open import Web.Semantic.DL.ABox.Model using
  ( _⊨a_ ; on-bnode ; bnodes ; _,_ ; ⊨a-resp-≲ )
open import Web.Semantic.DL.Category.Composition using ( _∙_ )
open import Web.Semantic.DL.Category.Properties.Composition.Assoc using
  ( compose-assoc )
open import Web.Semantic.DL.Category.Properties.Composition.Lemmas using
  ( compose-left ; compose-right ; compose-resp-⊨a )
open import Web.Semantic.DL.Category.Properties.Composition.RespectsEquiv using
  ( compose-resp-≣ )
open import Web.Semantic.DL.Category.Properties.Equivalence using
  ( ≣-refl ; ≣-sym ; ≣-trans )
open import Web.Semantic.DL.Category.Properties.Tensor.Coherence using
  ( symm-unit )
open import Web.Semantic.DL.Category.Properties.Tensor.Lemmas using
  ( tensor-up ; tensor-down ; tensor-resp-⊨a )
open import Web.Semantic.DL.Category.Properties.Tensor.SymmNatural using
  ( symm-natural )
open import Web.Semantic.DL.Category.Object using ( Object ; IN ; fin )
open import Web.Semantic.DL.Category.Morphism using
  ( _⇒_ ; BN ; impl ; _⊑_ ; _≣_ ; _,_ )
open import Web.Semantic.DL.Category.Tensor using ( _⟨⊗⟩_ )
open import Web.Semantic.DL.Category.Unit using ( I )
open import Web.Semantic.DL.Category.Wiring using
  ( wires-≈ ; wires-≈⁻¹ ; identity ; unit₁ ; unit₂ ; symm )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.DL.TBox.Interp using ( Δ ; _⊨_≈_ ; ≈-refl ; ≈-sym )
open import Web.Semantic.DL.TBox.Interp.Morphism using ( ≲-refl )
open import Web.Semantic.Util using
  ( _∘_ ; False ; _⊕_⊕_ ; inode ; bnode ; enode ; left ; right ; up ; down )

module Web.Semantic.DL.Category.Properties.Tensor.UnitNatural
  {Σ : Signature} {S T : TBox Σ} where

unit₁-natural : ∀ {A B : Object S T} (F : A ⇒ B) →
  ((identity I ⟨⊗⟩ F) ∙ unit₁ B ≣ unit₁ A ∙ F)
unit₁-natural {A} {B} F = (LHS⊑RHS , RHS⊑LHS) where

  LHS⊑RHS : ((identity I ⟨⊗⟩ F) ∙ unit₁ B ⊑ unit₁ A ∙ F)
  LHS⊑RHS J J⊨STA J⊨LHS = (f , J⊨RHS) where

    f : False ⊕ IN A ⊕ BN F → Δ ⌊ J ⌋
    f (inode ())
    f (bnode x) = ind J (inode (inj₂ x))
    f (enode v) = ind J (bnode (inode (inj₂ v)))

    f✓ : ∀ x → ⌊ J ⌋ ⊨ ind J (left (down x)) ≈ on-bnode f (ind J) (right x)
    f✓ (inode x) = ≈-refl ⌊ J ⌋
    f✓ (bnode v) = ≈-refl ⌊ J ⌋
    f✓ (enode y) = wires-≈ inj₂ (proj₂ (fin B) y) 
      (compose-right (identity I ⟨⊗⟩ F) (unit₁ B) J J⊨LHS)

    J⊨RHS : bnodes J f ⊨a impl (unit₁ A ∙ F)
    J⊨RHS = compose-resp-⊨a (unit₁ A) F (bnodes J f)
      (wires-≈⁻¹ inj₂ (λ x → ≈-refl ⌊ J ⌋) (proj₁ (fin A))) 
      (⊨a-resp-≲ (≲-refl ⌊ J ⌋ , f✓) (impl F)
        (tensor-down (identity I) F (left * J)
          (compose-left (identity I ⟨⊗⟩ F) (unit₁ B) J J⊨LHS)))

  RHS⊑LHS : (unit₁ A ∙ F ⊑ (identity I ⟨⊗⟩ F) ∙ unit₁ B)
  RHS⊑LHS J J⊨STA J⊨RHS = (f , J⊨LHS) where

    f : ((False ⊎ BN F) ⊕ (False ⊎ IN B) ⊕ False) → Δ ⌊ J ⌋
    f (inode (inj₁ ()))
    f (inode (inj₂ v)) = ind J (bnode (enode v))
    f (bnode (inj₁ ()))
    f (bnode (inj₂ y)) = ind J (enode y)
    f (enode ())

    f✓ : ∀ x → ⌊ J ⌋ ⊨ ind J (right x) ≈ on-bnode f (ind J) (left (down x))
    f✓ (inode x) = ≈-sym ⌊ J ⌋ (wires-≈ inj₂ (proj₂ (fin A) x) (compose-left (unit₁ A) F J J⊨RHS))
    f✓ (bnode v) = ≈-refl ⌊ J ⌋
    f✓ (enode y) = ≈-refl ⌊ J ⌋

    J⊨LHS : bnodes J f ⊨a impl ((identity I ⟨⊗⟩ F) ∙ unit₁ B)
    J⊨LHS = compose-resp-⊨a (identity I ⟨⊗⟩ F) (unit₁ B) (bnodes J f) 
      (tensor-resp-⊨a (identity I) F (left * bnodes J f) 
        (wires-≈⁻¹ {I = up * left * bnodes J f} (λ ()) (λ ()) []) 
        (⊨a-resp-≲ (≲-refl ⌊ J ⌋ , f✓) (impl F) 
          (compose-right (unit₁ A) F J J⊨RHS)))
      (wires-≈⁻¹ inj₂ (λ x → ≈-refl ⌊ J ⌋) (proj₁ (fin B)))

unit₂-natural : ∀ {A B : Object S T} (F : A ⇒ B) →
  ((F ⟨⊗⟩ identity I) ∙ unit₂ B ≣ unit₂ A ∙ F)
unit₂-natural {A} {B} F = 
  ≣-trans 
    (compose-resp-≣ (≣-refl (F ⟨⊗⟩ identity I)) (≣-sym (symm-unit B)))
  (≣-trans 
    (≣-sym (compose-assoc (F ⟨⊗⟩ identity I) (symm B I) (unit₁ B)))
  (≣-trans 
    (compose-resp-≣ (symm-natural F (identity I)) (≣-refl (unit₁ B))) 
  (≣-trans 
    (compose-assoc (symm A I) (identity I ⟨⊗⟩ F) (unit₁ B)) 
  (≣-trans 
    (compose-resp-≣ (≣-refl (symm A I)) (unit₁-natural F))
  (≣-trans 
    (≣-sym (compose-assoc (symm A I) (unit₁ A) F))
    (compose-resp-≣ (symm-unit A) (≣-refl F)))))))
