open import Data.Product using ( _×_ ; _,_ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox ; Assertions ; ⟨ABox⟩ ; ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.ABox.Interp using ( Interp ; _,_ ; ⌊_⌋ ; ind ; _*_ )
open import Web.Semantic.DL.ABox.Interp.Morphism using ( _≲_ ; _,_ ; ≲⌊_⌋ ; ≲-resp-ind )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox.Interp using ( Δ ; _⊨_≈_ ; ≈-refl ; ≈-sym ; ≈-trans ; con ; rol ; con-≈ ; rol-≈ )
open import Web.Semantic.DL.TBox.Interp.Morphism using ( ≲-image ; ≲-resp-≈ ; ≲-resp-con ; ≲-resp-rol )
open import Web.Semantic.Util using ( True ; tt ; _∘_ ; _⊕_⊕_ ; inode ; bnode ; enode )

module Web.Semantic.DL.ABox.Model {Σ : Signature} where

infixr 2 _⊨a_ _⊨b_

_⟦_⟧₀ : ∀ {X} (I : Interp Σ X) → X → (Δ ⌊ I ⌋)
I ⟦ x ⟧₀ = ind I x

_⊨a_ : ∀ {X} → Interp Σ X → ABox Σ X → Set
I ⊨a ε            = True
I ⊨a (A , B)      = (I ⊨a A) × (I ⊨a B)
I ⊨a x ∼ y        = ⌊ I ⌋ ⊨ ind I x ≈ ind I y
I ⊨a x ∈₁ c       = ind I x ∈ con ⌊ I ⌋ c
I ⊨a (x , y) ∈₂ r = (ind I x , ind I y) ∈ rol ⌊ I ⌋ r

Assertions✓ : ∀ {X} (I : Interp Σ X) A {a} → 
  (a ∈ Assertions A) → (I ⊨a A) → (I ⊨a a)
Assertions✓ I ε         ()         I⊨A
Assertions✓ I (A , B)   (inj₁ a∈A) (I⊨A , I⊨B) = Assertions✓ I A a∈A I⊨A
Assertions✓ I (A , B)   (inj₂ a∈B) (I⊨A , I⊨B) = Assertions✓ I B a∈B I⊨B
Assertions✓ I (i ∼ j)   refl       I⊨A         = I⊨A
Assertions✓ I (i ∈₁ c)  refl       I⊨A         = I⊨A
Assertions✓ I (ij ∈₂ r) refl       I⊨A         = I⊨A

⊨a-resp-≲ : ∀ {X} {I J : Interp Σ X} → (I ≲ J) → ∀ A → (I ⊨a A) → (J ⊨a A)
⊨a-resp-≲ {X} {I} {J} I≲J ε I⊨A = 
  tt
⊨a-resp-≲ {X} {I} {J} I≲J (A , B) (I⊨A , I⊨B) = 
  (⊨a-resp-≲ I≲J A I⊨A , ⊨a-resp-≲ I≲J B I⊨B)
⊨a-resp-≲ {X} {I} {J} I≲J (x ∼ y)   I⊨x∼y = 
  ≈-trans ⌊ J ⌋ (≈-sym ⌊ J ⌋ (≲-resp-ind I≲J x)) 
    (≈-trans ⌊ J ⌋ (≲-resp-≈ ≲⌊ I≲J ⌋ I⊨x∼y) 
      (≲-resp-ind I≲J y))
⊨a-resp-≲ {X} {I} {J} I≲J (x ∈₁ c)  I⊨x∈c = 
  con-≈ ⌊ J ⌋ c (≲-resp-con ≲⌊ I≲J ⌋ I⊨x∈c) (≲-resp-ind I≲J x)
⊨a-resp-≲ {X} {I} {J} I≲J ((x , y) ∈₂ r) I⊨xy∈r = 
  rol-≈ ⌊ J ⌋ r (≈-sym ⌊ J ⌋ (≲-resp-ind I≲J x)) 
    (≲-resp-rol ≲⌊ I≲J ⌋ I⊨xy∈r) (≲-resp-ind I≲J y)

⟨Abox⟩-resp-⊨ : ∀ {I X Y i j} (f : X → Y) → (∀ x → I ⊨ i x ≈ j (f x)) →
  ∀ A → (I , i ⊨a A) → (I , j ⊨a ⟨ABox⟩ f A)
⟨Abox⟩-resp-⊨ {I} f i≈j∘f ε I⊨ε = 
  tt
⟨Abox⟩-resp-⊨ {I} f i≈j∘f (A , B) (I⊨A , I⊨B) = 
  (⟨Abox⟩-resp-⊨ f i≈j∘f A I⊨A , ⟨Abox⟩-resp-⊨ f i≈j∘f B I⊨B)
⟨Abox⟩-resp-⊨ {I} f i≈j∘f (x ∼ y) x≈y = 
  ≈-trans I (≈-sym I (i≈j∘f x)) (≈-trans I x≈y (i≈j∘f y))
⟨Abox⟩-resp-⊨ {I} f i≈j∘f (x ∈₁ c) x∈⟦c⟧ =
  con-≈ I c x∈⟦c⟧ (i≈j∘f x)
⟨Abox⟩-resp-⊨ {I} f i≈j∘f ((x , y) ∈₂ r) xy∈⟦r⟧ =
  rol-≈ I r (≈-sym I (i≈j∘f x)) xy∈⟦r⟧ (i≈j∘f y)

*-resp-⟨ABox⟩ : ∀ {X Y} (f : Y → X) I A →
  (I ⊨a ⟨ABox⟩ f A) → (f * I ⊨a A)
*-resp-⟨ABox⟩ f (I , i) ε I⊨ε = 
  tt
*-resp-⟨ABox⟩ f (I , i) (A , B) (I⊨A , I⊨B) = 
  (*-resp-⟨ABox⟩ f (I , i) A I⊨A , *-resp-⟨ABox⟩ f (I , i) B I⊨B )
*-resp-⟨ABox⟩ f (I , i) (x ∼ y) x≈y = 
  x≈y
*-resp-⟨ABox⟩ f (I , i) (x ∈₁ c) x∈⟦c⟧ = 
  x∈⟦c⟧
*-resp-⟨ABox⟩ f (I , i) ((x , y) ∈₂ r) xy∈⟦c⟧ = 
  xy∈⟦c⟧

-- bnodes I f is the same as I, except that f is used as the interpretation
-- for bnodes.

on-bnode : ∀ {V W X Y Z} → (W → Z) → ((X ⊕ V ⊕ Y) → Z) → 
  ((X ⊕ W ⊕ Y) → Z)
on-bnode f g (inode x) = g (inode x)
on-bnode f g (bnode w) = f w
on-bnode f g (enode y) = g (enode y)

bnodes : ∀ {V W X Y} → (I : Interp Σ (X ⊕ V ⊕ Y)) → (W → Δ ⌊ I ⌋) → 
  Interp Σ (X ⊕ W ⊕ Y)
bnodes I f = (⌊ I ⌋ , on-bnode f (ind I))

bnodes-resp-≲ : ∀ {V W X Y} (I J : Interp Σ (X ⊕ V ⊕ Y)) →
  (I≲J : I ≲ J) → (f : W → Δ ⌊ I ⌋) → 
    (bnodes I f ≲ bnodes J (≲-image ≲⌊ I≲J ⌋ ∘ f))
bnodes-resp-≲ (I , i) (J , j) (I≲J , i≲j) f = (I≲J , lemma) where

  lemma : ∀ x → 
    J ⊨ ≲-image I≲J (on-bnode f i x) ≈ on-bnode (≲-image I≲J ∘ f) j x
  lemma (inode x) = i≲j (inode x)
  lemma (bnode v) = ≈-refl J
  lemma (enode y) = i≲j (enode y)

-- I ⊨b A whenever there exists an f such that bnodes I f ⊨a A

data _⊨b_ {V W X Y} (I : Interp Σ (X ⊕ V ⊕ Y)) 
  (A : ABox Σ (X ⊕ W ⊕ Y)) : Set where
    _,_ : ∀ f → (bnodes I f ⊨a A) → (I ⊨b A)

⊨b-resp-≲ : ∀ {V W X Y} {I J : Interp Σ (X ⊕ V ⊕ Y)} → (I ≲ J) 
  → ∀ (A : ABox Σ (X ⊕ W ⊕ Y)) → (I ⊨b A) → (J ⊨b A)
⊨b-resp-≲ I≲J A (f , I⊨A) = 
  ((≲-image ≲⌊ I≲J ⌋ ∘ f) , ⊨a-resp-≲ (bnodes-resp-≲ _ _ I≲J f) A I⊨A)

