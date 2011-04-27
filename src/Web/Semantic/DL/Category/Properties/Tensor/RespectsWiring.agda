open import Data.Product using ( proj₁ ; proj₂ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality using
  ( _≡_ ; refl ; sym ; cong )
open import Relation.Unary using ( _⊆_ )
open import Web.Semantic.DL.ABox using ( ABox ; ⟨ABox⟩ ; Assertions )
open import Web.Semantic.DL.ABox.Interp using ( ⌊_⌋ ; ind )
open import Web.Semantic.DL.ABox.Model using ( _⊨a_ ; bnodes ; _,_ )
open import Web.Semantic.DL.Category.Object using ( Object ; IN ; fin ; iface )
open import Web.Semantic.DL.Category.Morphism using ( impl ; _≣_ ; _⊑_ ; _,_ )
open import Web.Semantic.DL.Category.Tensor using ( _⊗_ ; _⟨⊗⟩_ )
open import Web.Semantic.DL.Category.Properties.Tensor.Lemmas using
  ( tensor-up ; tensor-down ; tensor-resp-⊨a )
open import Web.Semantic.DL.Category.Wiring using
  ( wiring ; wires-≈ ; wires-≈⁻¹ ; identity ; id✓ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.DL.TBox.Interp using
  ( Δ ; _⊨_≈_ ; ≈-refl ; ≈-refl′ ; ≈-trans )
open import Web.Semantic.Util using
  ( id ; _∘_ ; False ; elim ; inj⁻¹ ; _⊕_⊕_ ; inode ; bnode ; enode )

module Web.Semantic.DL.Category.Properties.Tensor.RespectsWiring
  {Σ : Signature} {S T : TBox Σ} where
 
tensor-resp-wiring : ∀ (A₁ A₂ B₁ B₂ : Object S T) →
  (f₁ : IN B₁ → IN A₁) → 
  (f₁✓ : Assertions (⟨ABox⟩ f₁ (iface B₁)) ⊆ Assertions (iface A₁)) → 
  (f₂ : IN B₂ → IN A₂) →
  (f₂✓ : Assertions (⟨ABox⟩ f₂ (iface B₂)) ⊆ Assertions (iface A₂)) → 
  (g : IN (B₁ ⊗ B₂) → IN (A₁ ⊗ A₂)) →
  (g✓ : Assertions (⟨ABox⟩ g (iface (B₁ ⊗ B₂))) ⊆ Assertions (iface (A₁ ⊗ A₂))) → 
    (∀ x → inj₁ (f₁ x) ≡ g (inj₁ x)) → 
      (∀ x → inj₂ (f₂ x) ≡ g (inj₂ x)) → 
        ((wiring A₁ B₁ f₁ f₁✓ ⟨⊗⟩ wiring A₂ B₂ f₂ f₂✓) ≣ 
          (wiring (A₁ ⊗ A₂) (B₁ ⊗ B₂) g g✓))
tensor-resp-wiring A₁ A₂ B₁ B₂ f₁ f₁✓ f₂ f₂✓ g g✓ f₁≡g₁ f₂≡g₂ = 
  (LHS⊑RHS , RHS⊑LHS) where

  LHS⊑RHS : 
    wiring A₁ B₁ f₁ f₁✓ ⟨⊗⟩ wiring A₂ B₂ f₂ f₂✓ ⊑ 
      wiring (A₁ ⊗ A₂) (B₁ ⊗ B₂) g g✓
  LHS⊑RHS I I⊨STA I⊨F = (elim , I⊨RHS) where

    lemma : ∀ x → ⌊ I ⌋ ⊨ ind I (inode (g x)) ≈ ind I (enode x)
    lemma (inj₁ x) = ≈-trans ⌊ I ⌋ 
      (≈-refl′ ⌊ I ⌋ (cong (ind I ∘ inode) (sym (f₁≡g₁ x))))
      (wires-≈ f₁ (proj₂ (fin B₁) x) 
        (tensor-up (wiring A₁ B₁ f₁ f₁✓) (wiring A₂ B₂ f₂ f₂✓) I I⊨F))
    lemma (inj₂ x) = ≈-trans ⌊ I ⌋ 
      (≈-refl′ ⌊ I ⌋ (cong (ind I ∘ inode) (sym (f₂≡g₂ x)))) 
      (wires-≈ f₂ (proj₂ (fin B₂) x) 
        (tensor-down (wiring A₁ B₁ f₁ f₁✓) (wiring A₂ B₂ f₂ f₂✓) I I⊨F))

    I⊨RHS : bnodes I elim ⊨a impl (wiring (A₁ ⊗ A₂) (B₁ ⊗ B₂) g g✓)
    I⊨RHS = wires-≈⁻¹ g lemma (proj₁ (fin (B₁ ⊗ B₂)))

  RHS⊑LHS : 
    wiring (A₁ ⊗ A₂) (B₁ ⊗ B₂) g g✓ ⊑
      wiring A₁ B₁ f₁ f₁✓ ⟨⊗⟩ wiring A₂ B₂ f₂ f₂✓
  RHS⊑LHS I I⊨STA I⊨F = (elim ∘ inj⁻¹ , I⊨LHS) where

    lemma₁ : ∀ x → ⌊ I ⌋ ⊨ ind I (inode (inj₁ (f₁ x))) ≈ ind I (enode (inj₁ x))
    lemma₁ x = ≈-trans ⌊ I ⌋ 
      (≈-refl′ ⌊ I ⌋ (cong (ind I ∘ inode) (f₁≡g₁ x))) 
      (wires-≈ g (proj₂ (fin (B₁ ⊗ B₂)) (inj₁ x)) I⊨F)

    lemma₂ : ∀ x → ⌊ I ⌋ ⊨ ind I (inode (inj₂ (f₂ x))) ≈ ind I (enode (inj₂ x))
    lemma₂ x = ≈-trans ⌊ I ⌋ 
      (≈-refl′ ⌊ I ⌋ (cong (ind I ∘ inode) (f₂≡g₂ x))) 
      (wires-≈ g (proj₂ (fin (B₁ ⊗ B₂)) (inj₂ x)) I⊨F)

    I⊨LHS : bnodes I (elim ∘ inj⁻¹) ⊨a impl (wiring A₁ B₁ f₁ f₁✓ ⟨⊗⟩ wiring A₂ B₂ f₂ f₂✓)
    I⊨LHS = tensor-resp-⊨a (wiring A₁ B₁ f₁ f₁✓) (wiring A₂ B₂ f₂ f₂✓) (bnodes I (elim ∘ inj⁻¹)) 
      (wires-≈⁻¹ f₁ lemma₁ (proj₁ (fin B₁))) (wires-≈⁻¹ f₂ lemma₂ (proj₁ (fin B₂))) 
