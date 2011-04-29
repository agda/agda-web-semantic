open import Data.Product using ( proj₁ ; proj₂ )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Web.Semantic.DL.ABox.Interp using ( ⌊_⌋ ; ind ; _*_ )
open import Web.Semantic.DL.ABox.Interp.Morphism using ( _,_ )
open import Web.Semantic.DL.ABox.Model using
  ( _⊨a_ ; on-bnode ; bnodes ; _,_ ; ⊨a-resp-≲ )
open import Web.Semantic.DL.Category.Composition using ( _∙_ )
open import Web.Semantic.DL.Category.Properties.Composition.Lemmas using
  ( compose-left ; compose-right ; compose-resp-⊨a )
open import Web.Semantic.DL.Category.Properties.Tensor.Lemmas using
  ( tensor-up ; tensor-down ; tensor-resp-⊨a )
open import Web.Semantic.DL.Category.Object using ( Object ; IN ; fin )
open import Web.Semantic.DL.Category.Morphism using
  ( _⇒_ ; BN ; impl ; _⊑_ ; _≣_ ; _,_ )
open import Web.Semantic.DL.Category.Tensor using ( _⊗_ ; _⟨⊗⟩_ )
open import Web.Semantic.DL.Category.Unit using ( I )
open import Web.Semantic.DL.Category.Wiring using
  ( wires-≈ ; wires-≈⁻¹ ; symm )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.DL.TBox.Interp using ( Interp ; Δ ; _⊨_≈_ ; ≈-refl ; ≈-sym )
open import Web.Semantic.DL.TBox.Interp.Morphism using ( ≲-refl )
open import Web.Semantic.Util using
  ( _∘_ ; False ; ⊎-swap
  ; _⊕_⊕_ ; inode ; bnode ; enode ; left ; right ; up ; down )

module Web.Semantic.DL.Category.Properties.Tensor.SymmNatural
  {Σ : Signature} {S T : TBox Σ} where

symm-natural : ∀ {A₁ A₂ B₁ B₂ : Object S T} (F₁ : A₁ ⇒ B₁) (F₂ : A₂ ⇒ B₂) →
  ((F₁ ⟨⊗⟩ F₂) ∙ symm B₁ B₂ ≣ symm A₁ A₂ ∙ (F₂ ⟨⊗⟩ F₁))
symm-natural {A₁} {A₂} {B₁} {B₂} F₁ F₂ = (LHS⊑RHS , RHS⊑LHS) where

  LHS⊑RHS : (F₁ ⟨⊗⟩ F₂) ∙ symm B₁ B₂ ⊑ symm A₁ A₂ ∙ (F₂ ⟨⊗⟩ F₁)
  LHS⊑RHS J J⊨STA J⊨LHS = (f , J⊨RHS) where

    f : False ⊕ (IN A₂ ⊎ IN A₁) ⊕ (BN F₂ ⊎ BN F₁) → Δ ⌊ J ⌋
    f (inode ())
    f (bnode (inj₁ x)) = ind J (inode (inj₂ x))
    f (bnode (inj₂ x)) = ind J (inode (inj₁ x))
    f (enode (inj₁ v)) = ind J (bnode (inode (inj₂ v)))
    f (enode (inj₂ v)) = ind J (bnode (inode (inj₁ v)))

    lemma₀ : ∀ x → 
      ⌊ J ⌋ ⊨ ind J (inode (⊎-swap x)) ≈ f (bnode x)
    lemma₀ (inj₁ x) = ≈-refl ⌊ J ⌋
    lemma₀ (inj₂ y) = ≈-refl ⌊ J ⌋

    lemma₁ : ∀ x → 
      ⌊ J ⌋ ⊨ ind J (left (up x)) ≈ on-bnode f (ind J) (right (down x))
    lemma₁ (inode x) = ≈-refl ⌊ J ⌋
    lemma₁ (bnode v) = ≈-refl ⌊ J ⌋
    lemma₁ (enode y) = wires-≈ ⊎-swap (proj₂ (fin (B₂ ⊗ B₁)) (inj₂ y)) 
      (compose-right (F₁ ⟨⊗⟩ F₂) (symm B₁ B₂) J J⊨LHS)

    lemma₂ : ∀ x → 
      ⌊ J ⌋ ⊨ ind J (left (down x)) ≈ on-bnode f (ind J) (right (up x))
    lemma₂ (inode x) = ≈-refl ⌊ J ⌋
    lemma₂ (bnode v) = ≈-refl ⌊ J ⌋
    lemma₂ (enode y) = wires-≈ ⊎-swap (proj₂ (fin (B₂ ⊗ B₁)) (inj₁ y))
      (compose-right (F₁ ⟨⊗⟩ F₂) (symm B₁ B₂) J J⊨LHS)

    J⊨RHS : bnodes J f ⊨a impl (symm A₁ A₂ ∙ (F₂ ⟨⊗⟩ F₁))
    J⊨RHS = compose-resp-⊨a (symm A₁ A₂) (F₂ ⟨⊗⟩ F₁) (bnodes J f) 
      (wires-≈⁻¹ ⊎-swap lemma₀ (proj₁ (fin (A₂ ⊗ A₁)))) 
      (tensor-resp-⊨a F₂ F₁ (right * bnodes J f) 
        (⊨a-resp-≲ (≲-refl ⌊ J ⌋ , lemma₂) (impl F₂) 
          (tensor-down F₁ F₂ (left * J) 
            (compose-left (F₁ ⟨⊗⟩ F₂) (symm B₁ B₂) J J⊨LHS)))
        (⊨a-resp-≲ (≲-refl ⌊ J ⌋ , lemma₁) (impl F₁)
          (tensor-up F₁ F₂ (left * J)
            (compose-left (F₁ ⟨⊗⟩ F₂) (symm B₁ B₂) J J⊨LHS))))

  RHS⊑LHS : symm A₁ A₂ ∙ (F₂ ⟨⊗⟩ F₁) ⊑ (F₁ ⟨⊗⟩ F₂) ∙ symm B₁ B₂
  RHS⊑LHS J J⊨STA J⊨RHS = (f , J⊨LHS) where

    f : ((BN F₁ ⊎ BN F₂) ⊕ (IN B₁ ⊎ IN B₂) ⊕ False) → Δ ⌊ J ⌋
    f (inode (inj₁ v)) = ind J (bnode (enode (inj₂ v)))
    f (inode (inj₂ v)) = ind J (bnode (enode (inj₁ v)))
    f (bnode (inj₁ y)) = ind J (enode (inj₂ y))
    f (bnode (inj₂ y)) = ind J (enode (inj₁ y))
    f (enode ())

    lemma₀ : ∀ x → ⌊ J ⌋ ⊨ f (bnode (⊎-swap x)) ≈ ind J (enode x)
    lemma₀ (inj₁ y) = ≈-refl ⌊ J ⌋
    lemma₀ (inj₂ y) = ≈-refl ⌊ J ⌋

    lemma₁ : ∀ x →
      ⌊ J ⌋ ⊨ ind J (right (down x)) ≈ on-bnode f (ind J) (left (up x))
    lemma₁ (inode x) = ≈-sym ⌊ J ⌋
      (wires-≈ ⊎-swap (proj₂ (fin (A₂ ⊗ A₁)) (inj₂ x))
        (compose-left (symm A₁ A₂) (F₂ ⟨⊗⟩ F₁) J J⊨RHS))
    lemma₁ (bnode v) = ≈-refl ⌊ J ⌋
    lemma₁ (enode y) = ≈-refl ⌊ J ⌋

    lemma₂ : ∀ x → 
      ⌊ J ⌋ ⊨ ind J (right (up x)) ≈ on-bnode f (ind J) (left (down x))
    lemma₂ (inode x) = ≈-sym ⌊ J ⌋
      (wires-≈ ⊎-swap (proj₂ (fin (A₂ ⊗ A₁)) (inj₁ x))
        (compose-left (symm A₁ A₂) (F₂ ⟨⊗⟩ F₁) J J⊨RHS))
    lemma₂ (bnode v) = ≈-refl ⌊ J ⌋
    lemma₂ (enode y) = ≈-refl ⌊ J ⌋

    J⊨LHS : bnodes J f ⊨a impl ((F₁ ⟨⊗⟩ F₂) ∙ symm B₁ B₂)
    J⊨LHS = compose-resp-⊨a (F₁ ⟨⊗⟩ F₂) (symm B₁ B₂) (bnodes J f)
      (tensor-resp-⊨a F₁ F₂ (left * bnodes J f)
        (⊨a-resp-≲ (≲-refl ⌊ J ⌋ , lemma₁) (impl F₁)
          (tensor-down F₂ F₁ (right * J)
            (compose-right (symm A₁ A₂) (F₂ ⟨⊗⟩ F₁) J J⊨RHS)))
        (⊨a-resp-≲ (≲-refl ⌊ J ⌋ , lemma₂) (impl F₂)
          (tensor-up F₂ F₁ (right * J)
            (compose-right (symm A₁ A₂) (F₂ ⟨⊗⟩ F₁) J J⊨RHS))))
      (wires-≈⁻¹ ⊎-swap lemma₀ (proj₁ (fin (B₂ ⊗ B₁))))