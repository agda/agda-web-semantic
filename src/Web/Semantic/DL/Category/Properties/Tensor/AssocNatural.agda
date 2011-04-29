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
  ( wires-≈ ; wires-≈⁻¹ ; assoc )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.DL.TBox.Interp using
  ( Δ ; _⊨_≈_ ; ≈-refl ; ≈-refl′ ; ≈-sym )
open import Web.Semantic.DL.TBox.Interp.Morphism using ( ≲-refl )
open import Web.Semantic.Util using
  ( _∘_ ; False ; ⊎-assoc ; ⊎-assoc⁻¹
  ; _⊕_⊕_ ; inode ; bnode ; enode ; left ; right ; up ; down )

module Web.Semantic.DL.Category.Properties.Tensor.AssocNatural
  {Σ : Signature} {S T : TBox Σ} where

assoc-natural : ∀ {A₁ A₂ A₃ B₁ B₂ B₃ : Object S T} 
  (F₁ : A₁ ⇒ B₁) (F₂ : A₂ ⇒ B₂) (F₃ : A₃ ⇒ B₃) →
    (((F₁ ⟨⊗⟩ F₂) ⟨⊗⟩ F₃) ∙ assoc B₁ B₂ B₃ ≣
      assoc A₁ A₂ A₃ ∙ (F₁ ⟨⊗⟩ (F₂ ⟨⊗⟩ F₃)))
assoc-natural {A₁} {A₂} {A₃} {B₁} {B₂} {B₃} F₁ F₂ F₃ = (LHS⊑RHS , RHS⊑LHS) where

  LHS⊑RHS : ((F₁ ⟨⊗⟩ F₂) ⟨⊗⟩ F₃) ∙ assoc B₁ B₂ B₃ ⊑
    assoc A₁ A₂ A₃ ∙ (F₁ ⟨⊗⟩ (F₂ ⟨⊗⟩ F₃))
  LHS⊑RHS J J⊨STA J⊨LHS = (f , J⊨RHS) where

    f : (False ⊕ (IN A₁ ⊎ (IN A₂ ⊎ IN A₃)) ⊕ (BN F₁ ⊎ (BN F₂ ⊎ BN F₃))) → Δ ⌊ J ⌋
    f (inode ())
    f (bnode x) = ind J (inode (⊎-assoc⁻¹ x))
    f (enode v) = ind J (bnode (inode (⊎-assoc⁻¹ v)))

    lemma₁ : ∀ x → 
      ⌊ J ⌋ ⊨ ind J (left (up (up x))) ≈ 
        on-bnode f (ind J) (right (up x))
    lemma₁ (inode x) = ≈-refl ⌊ J ⌋
    lemma₁ (bnode v) = ≈-refl ⌊ J ⌋
    lemma₁ (enode y) = wires-≈ ⊎-assoc⁻¹
      (proj₂ (fin (B₁ ⊗ (B₂ ⊗ B₃))) (inj₁ y)) 
      (compose-right ((F₁ ⟨⊗⟩ F₂) ⟨⊗⟩ F₃) (assoc B₁ B₂ B₃) J J⊨LHS)

    lemma₂ : ∀ x → 
      ⌊ J ⌋ ⊨ ind J (left (up (down x))) ≈
        on-bnode f (ind J) (right (down (up x)))
    lemma₂ (inode x) = ≈-refl ⌊ J ⌋
    lemma₂ (bnode v) = ≈-refl ⌊ J ⌋
    lemma₂ (enode y) = wires-≈ ⊎-assoc⁻¹
      (proj₂ (fin (B₁ ⊗ (B₂ ⊗ B₃))) (inj₂ (inj₁ y))) 
      (compose-right ((F₁ ⟨⊗⟩ F₂) ⟨⊗⟩ F₃) (assoc B₁ B₂ B₃) J J⊨LHS)

    lemma₃ : ∀ x → 
      ⌊ J ⌋ ⊨ ind J (left (down x)) ≈
        on-bnode f (ind J) (right (down (down x)))
    lemma₃ (inode x) = ≈-refl ⌊ J ⌋
    lemma₃ (bnode v) = ≈-refl ⌊ J ⌋
    lemma₃ (enode y) = wires-≈ ⊎-assoc⁻¹
      (proj₂ (fin (B₁ ⊗ (B₂ ⊗ B₃))) (inj₂ (inj₂ y))) 
      (compose-right ((F₁ ⟨⊗⟩ F₂) ⟨⊗⟩ F₃) (assoc B₁ B₂ B₃) J J⊨LHS)

    J⊨RHS : bnodes J f ⊨a impl (assoc A₁ A₂ A₃ ∙ (F₁ ⟨⊗⟩ (F₂ ⟨⊗⟩ F₃)))
    J⊨RHS = compose-resp-⊨a (assoc A₁ A₂ A₃) (F₁ ⟨⊗⟩ (F₂ ⟨⊗⟩ F₃)) (bnodes J f)
      (wires-≈⁻¹ ⊎-assoc⁻¹ (λ x → ≈-refl ⌊ J ⌋) (proj₁ (fin (A₁ ⊗ (A₂ ⊗ A₃)))))
      (tensor-resp-⊨a F₁ (F₂ ⟨⊗⟩ F₃) (right * bnodes J f) 
        (⊨a-resp-≲ (≲-refl ⌊ J ⌋ , lemma₁) (impl F₁) 
          (tensor-up F₁ F₂ (up * left * J) 
            (tensor-up (F₁ ⟨⊗⟩ F₂) F₃ (left * J)
              (compose-left ((F₁ ⟨⊗⟩ F₂) ⟨⊗⟩ F₃) (assoc B₁ B₂ B₃) J J⊨LHS))))
        (tensor-resp-⊨a F₂ F₃ (down * right * bnodes J f) 
          (⊨a-resp-≲ (≲-refl ⌊ J ⌋ , lemma₂) (impl F₂)
            (tensor-down F₁ F₂ (up * left * J)
              (tensor-up (F₁ ⟨⊗⟩ F₂) F₃ (left * J)
                (compose-left ((F₁ ⟨⊗⟩ F₂) ⟨⊗⟩ F₃) (assoc B₁ B₂ B₃) J J⊨LHS)))) 
          (⊨a-resp-≲ (≲-refl ⌊ J ⌋ , lemma₃) (impl F₃)
            (tensor-down (F₁ ⟨⊗⟩ F₂) F₃ (left * J)
              (compose-left ((F₁ ⟨⊗⟩ F₂) ⟨⊗⟩ F₃) (assoc B₁ B₂ B₃) J J⊨LHS)))))

  RHS⊑LHS : assoc A₁ A₂ A₃ ∙ (F₁ ⟨⊗⟩ (F₂ ⟨⊗⟩ F₃)) ⊑
    ((F₁ ⟨⊗⟩ F₂) ⟨⊗⟩ F₃) ∙ assoc B₁ B₂ B₃
  RHS⊑LHS J J⊨STA J⊨RHS = (f , J⊨LHS) where

    f : (((BN F₁ ⊎ BN F₂) ⊎ BN F₃) ⊕ ((IN B₁ ⊎ IN B₂) ⊎ IN B₃) ⊕ False) → Δ ⌊ J ⌋
    f (inode v) = ind J (bnode (enode (⊎-assoc v)))
    f (bnode y) = ind J (enode (⊎-assoc y))
    f (enode ())

    lemma₀ : ∀ x → 
      ⌊ J ⌋ ⊨ ind J (enode (⊎-assoc (⊎-assoc⁻¹ x))) ≈ ind J (enode x)
    lemma₀ (inj₁ x) = ≈-refl ⌊ J ⌋
    lemma₀ (inj₂ (inj₁ x)) = ≈-refl ⌊ J ⌋
    lemma₀ (inj₂ (inj₂ y)) = ≈-refl ⌊ J ⌋

    lemma₁ : ∀ x → ⌊ J ⌋ ⊨ ind J (right (up x)) ≈
      on-bnode f (ind J) (left (up (up x)))
    lemma₁ (inode x) = ≈-sym ⌊ J ⌋ (wires-≈ ⊎-assoc⁻¹ 
      (proj₂ (fin (A₁ ⊗ (A₂ ⊗ A₃))) (inj₁ x))
      (compose-left (assoc A₁ A₂ A₃) (F₁ ⟨⊗⟩ (F₂ ⟨⊗⟩ F₃)) J J⊨RHS))
    lemma₁ (bnode v) = ≈-refl ⌊ J ⌋
    lemma₁ (enode y) = ≈-refl ⌊ J ⌋

    lemma₂ : ∀ x → ⌊ J ⌋ ⊨ ind J (right (down (up x))) ≈
      on-bnode f (ind J) (left (up (down x)))
    lemma₂ (inode x) = ≈-sym ⌊ J ⌋ (wires-≈ ⊎-assoc⁻¹ 
      (proj₂ (fin (A₁ ⊗ (A₂ ⊗ A₃))) (inj₂ (inj₁ x)))
      (compose-left (assoc A₁ A₂ A₃) (F₁ ⟨⊗⟩ (F₂ ⟨⊗⟩ F₃)) J J⊨RHS))
    lemma₂ (bnode v) = ≈-refl ⌊ J ⌋
    lemma₂ (enode y) = ≈-refl ⌊ J ⌋

    lemma₃ : ∀ x → ⌊ J ⌋ ⊨ ind J (right (down (down x))) ≈
      on-bnode f (ind J) (left (down x))
    lemma₃ (inode x) = ≈-sym ⌊ J ⌋ (wires-≈ ⊎-assoc⁻¹ 
      (proj₂ (fin (A₁ ⊗ (A₂ ⊗ A₃))) (inj₂ (inj₂ x)))
      (compose-left (assoc A₁ A₂ A₃) (F₁ ⟨⊗⟩ (F₂ ⟨⊗⟩ F₃)) J J⊨RHS))
    lemma₃ (bnode v) = ≈-refl ⌊ J ⌋
    lemma₃ (enode y) = ≈-refl ⌊ J ⌋

    J⊨LHS : bnodes J f ⊨a impl (((F₁ ⟨⊗⟩ F₂) ⟨⊗⟩ F₃) ∙ assoc B₁ B₂ B₃)
    J⊨LHS = compose-resp-⊨a ((F₁ ⟨⊗⟩ F₂) ⟨⊗⟩ F₃) (assoc B₁ B₂ B₃) (bnodes J f)
      (tensor-resp-⊨a (F₁ ⟨⊗⟩ F₂) F₃ (left * bnodes J f) 
        (tensor-resp-⊨a F₁ F₂ (up * left * bnodes J f)
          (⊨a-resp-≲ (≲-refl ⌊ J ⌋ , lemma₁) (impl F₁) 
            (tensor-up F₁ (F₂ ⟨⊗⟩ F₃) (right * J) 
              (compose-right (assoc A₁ A₂ A₃) (F₁ ⟨⊗⟩ (F₂ ⟨⊗⟩ F₃)) J J⊨RHS))) 
          (⊨a-resp-≲ (≲-refl ⌊ J ⌋ , lemma₂) (impl F₂) 
            (tensor-up F₂ F₃ (down * right * J) 
              (tensor-down F₁ (F₂ ⟨⊗⟩ F₃) (right * J)
                (compose-right (assoc A₁ A₂ A₃) (F₁ ⟨⊗⟩ (F₂ ⟨⊗⟩ F₃)) J J⊨RHS))))) 
       (⊨a-resp-≲ (≲-refl ⌊ J ⌋ , lemma₃) (impl F₃)
         (tensor-down F₂ F₃ (down * right * J)
           (tensor-down F₁ (F₂ ⟨⊗⟩ F₃) (right * J)
             (compose-right (assoc A₁ A₂ A₃) (F₁ ⟨⊗⟩ (F₂ ⟨⊗⟩ F₃)) J J⊨RHS))))) 
      (wires-≈⁻¹ ⊎-assoc⁻¹ lemma₀ (proj₁ (fin (B₁ ⊗ (B₂ ⊗ B₃)))))
