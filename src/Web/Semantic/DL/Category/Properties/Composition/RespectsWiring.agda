open import Data.Product using ( proj₁ ; proj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; sym ; cong )
open import Relation.Unary using ( _⊆_ )
open import Web.Semantic.DL.ABox using ( ABox ; ⟨ABox⟩ ; Assertions )
open import Web.Semantic.DL.ABox.Interp using ( ⌊_⌋ ; ind )
open import Web.Semantic.DL.ABox.Model using ( _⊨a_ ; bnodes ; _,_ )
open import Web.Semantic.DL.Category.Object using ( Object ; IN ; fin ; iface )
open import Web.Semantic.DL.Category.Morphism using ( impl ; _≣_ ; _⊑_ ; _,_ )
open import Web.Semantic.DL.Category.Composition using ( _∙_ )
open import Web.Semantic.DL.Category.Properties.Composition.Lemmas using
  ( compose-left ; compose-right ; compose-resp-⊨a )
open import Web.Semantic.DL.Category.Wiring using
  ( wiring ; wires-≈ ; wires-≈⁻¹ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.DL.TBox.Interp using
  ( Δ ; _⊨_≈_ ; ≈-refl ; ≈-refl′ ; ≈-trans )
open import Web.Semantic.Util using
  ( _∘_ ; False ; elim ; _⊕_⊕_ ; inode ; bnode ; enode )

module Web.Semantic.DL.Category.Properties.Composition.RespectsWiring
  {Σ : Signature} {S T : TBox Σ} where

compose-resp-wiring : ∀ (A B C : Object S T) →
  (f : IN B → IN A) → 
  (f✓ : Assertions (⟨ABox⟩ f (iface B)) ⊆ Assertions (iface A)) → 
  (g : IN C → IN B) →
  (g✓ : Assertions (⟨ABox⟩ g (iface C)) ⊆ Assertions (iface B)) → 
  (h : IN C → IN A) →
  (h✓ : Assertions (⟨ABox⟩ h (iface C)) ⊆ Assertions (iface A)) → 
    (∀ x → f (g x) ≡ h x) → 
      (wiring A B f f✓ ∙ wiring B C g g✓ ≣ wiring A C h h✓)
compose-resp-wiring A B C f f✓ g g✓ h h✓ fg≡h = 
  (LHS⊑RHS , RHS⊑LHS) where

  LHS⊑RHS : wiring A B f f✓ ∙ wiring B C g g✓ ⊑ wiring A C h h✓
  LHS⊑RHS I I⊨STA I⊨F = (elim , I⊨RHS) where

    lemma : ∀ x → ⌊ I ⌋ ⊨ ind I (inode (h x)) ≈ ind I (enode x)
    lemma x = ≈-trans ⌊ I ⌋ 
      (≈-refl′ ⌊ I ⌋ (cong (ind I ∘ inode) (sym (fg≡h x)))) 
      (≈-trans ⌊ I ⌋ 
        (wires-≈ f (proj₂ (fin B) (g x)) 
          (compose-left (wiring A B f f✓) (wiring B C g g✓) I I⊨F)) 
        (wires-≈ g (proj₂ (fin C) x) 
          (compose-right (wiring A B f f✓) (wiring B C g g✓) I I⊨F)))

    I⊨RHS : bnodes I elim ⊨a impl (wiring A C h h✓)
    I⊨RHS = wires-≈⁻¹ h lemma (proj₁ (fin C))

  RHS⊑LHS : wiring A C h h✓ ⊑ wiring A B f f✓ ∙ wiring B C g g✓
  RHS⊑LHS I I⊨STA I⊨F = (i , I⊨LHS) where

    i : (False ⊕ IN B ⊕ False) → Δ ⌊ I ⌋
    i (inode ())
    i (bnode y) = ind I (inode (f y))
    i (enode ())

    lemma : ∀ x → ⌊ I ⌋ ⊨ ind I (inode (f (g x))) ≈ ind I (enode x)
    lemma x = ≈-trans ⌊ I ⌋ 
      (≈-refl′ ⌊ I ⌋ (cong (ind I ∘ inode) (fg≡h x))) 
      (wires-≈ h (proj₂ (fin C) x) I⊨F)

    I⊨LHS : bnodes I i ⊨a impl (wiring A B f f✓ ∙ wiring B C g g✓)
    I⊨LHS = compose-resp-⊨a (wiring A B f f✓) (wiring B C g g✓) (bnodes I i) 
      (wires-≈⁻¹ f (λ x → ≈-refl ⌊ I ⌋) (proj₁ (fin B))) 
      (wires-≈⁻¹ g lemma (proj₁ (fin C)))
