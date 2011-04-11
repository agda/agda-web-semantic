open import Data.Product using ( _×_ ; _,_ )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox ; ⟨ABox⟩ )
open import Web.Semantic.DL.ABox.Interp using ( Interp ; _,_ ; ⌊_⌋ ; ind ; _*_ ; emp )
open import Web.Semantic.DL.ABox.Interp.Morphism using ( _≲_ ; _,_ ; ≲⌊_⌋ ; ≲-resp-ind ; _≋_ ; _**_ )
open import Web.Semantic.DL.ABox.Model using ( _⊨a_ ; ⟨Abox⟩-resp-⊨ ; *-resp-⟨ABox⟩ ; ⊨a-resp-≡ )
open import Web.Semantic.DL.Integrity using ( _⊕_⊨_ ; Initial ; Mediator ; Mediated ; _,_ )
open import Web.Semantic.DL.KB using ( KB ; _,_ )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox.Interp using ( _⊨_≈_ ; ≈-refl )
open import Web.Semantic.DL.TBox.Interp.Morphism using ( morph ; ≲-image )
open import Web.Semantic.Util using ( False ; _∘_ ; _⊕_⊕_ ; bnode ; inode ; enode )

module Web.Semantic.DL.Integrity.Closed {Σ : Signature} {X : Set} where

infixr 4 _,_

-- A closed-world variant on integrity constraints.

data Mediated₀ (I J : Interp Σ X) : Set where
  _,_ : (I≲J : I ≲ J) → (∀ (I≲₁J I≲₂J : I ≲ J) → (I≲₁J ≋ I≲₂J)) → Mediated₀ I J

data Initial₀ KB (I : Interp Σ X) : Set₁ where
  _,_ : (I ⊨ KB) → (∀ J → (J ⊨ KB) → Mediated₀ I J) → (I ∈ Initial₀ KB)

data _⊨₀_ (KB₁ KB₂ : KB Σ X) : Set₁ where
  _,_ : ∀ I → ((I ∈ Initial₀ KB₁) × (I ⊨ KB₂)) → (KB₁ ⊨₀ KB₂)

-- Closed-world ICs are given by specializing the open-world case
-- to the empty imported interpretion.

exp : KB Σ X → KB Σ (False ⊕ False ⊕ X)
exp (T , A) = (T , ⟨ABox⟩ enode A)

enode⁻¹ : (False ⊕ False ⊕ X) → X
enode⁻¹ (inode ())
enode⁻¹ (bnode ())
enode⁻¹ (enode x) = x

emp-≲ : ∀ (I : Interp Σ False) → (emp ≲ I)
emp-≲ I = (morph (λ ()) (λ {}) (λ ()) (λ {r} → λ {}) , λ ())

⊨₀-impl-⊨ : ∀ KB₁ KB₂ → (KB₁ ⊨₀ KB₂) → (emp ⊕ exp KB₁ ⊨ KB₂)
⊨₀-impl-⊨ (T , A) (U , B) (I , ((I⊨T , I⊨A) , I-med) , I⊨U , I⊨B) = 
  (I′ , I′-init , I⊨U , ⊨a-resp-≡ I (ind I) refl B I⊨B) where

  A′ : ABox Σ (False ⊕ False ⊕ X)
  A′ = ⟨ABox⟩ enode A

  I′ : Interp Σ (False ⊕ False ⊕ X)
  I′ = enode⁻¹ * I

  emp≲I′ : emp ≲ inode * I′
  emp≲I′ = emp-≲ (inode * I′)

  I′-med : Mediator emp I′ emp≲I′ (T , A′)
  I′-med J′ emp≲J′ (J′⊨T , J′⊨A′) = lemma (I-med J (J′⊨T , J⊨A)) where

    J : Interp Σ X
    J = enode * J′

    J⊨A : J ⊨a A
    J⊨A = *-resp-⟨ABox⟩ enode J′ A J′⊨A′

    lemma : Mediated₀ I J → Mediated emp I′ J′ emp≲I′ emp≲J′
    lemma ((I≲J , i≲j) , I≲J-uniq) = ((I≲J , i′≲j′) , (λ ()) , I′≲J′-uniq) where

      i′≲j′ : ∀ x → ⌊ J′ ⌋ ⊨ ≲-image I≲J (ind I (enode⁻¹ x)) ≈ ind J′ x
      i′≲j′ (inode ())
      i′≲j′ (bnode ())
      i′≲j′ (enode x) = i≲j x
 
      I′≲J′-uniq : ∀ (I≲₁J I≲₂J : I′ ≲ J′)_ _ →  I≲₁J ≋ I≲₂J
      I′≲J′-uniq I≲₁J I≲₂J _ _ = I≲J-uniq 
        (≲⌊ I≲₁J ⌋ , λ x → ≲-resp-ind I≲₁J (enode x)) 
        (≲⌊ I≲₂J ⌋ , λ x → ≲-resp-ind I≲₂J (enode x))

  I′⊨A′ : I′ ⊨a A′
  I′⊨A′ = ⟨Abox⟩-resp-⊨ enode (λ x → ≈-refl ⌊ I ⌋) A I⊨A

  I′-init : I′ ∈ Initial emp (T , A′)
  I′-init = ( emp-≲ (inode * I′) , (I⊨T , I′⊨A′) , I′-med )

⊨-impl-⊨₀ : ∀ KB₁ KB₂ → (emp ⊕ exp KB₁ ⊨ KB₂) → (KB₁ ⊨₀ KB₂)
⊨-impl-⊨₀ (T , A) (U , B) 
  (I′ , (emp≲I′ , (I′⊨T , I′⊨A) , I′-med) , I′⊨U , I′⊨B) = 
    (I , ((I′⊨T , I⊨A) , I-med) , I′⊨U , I′⊨B) where

  I : Interp Σ X
  I = enode * I′

  I⊨A : I ⊨a A
  I⊨A = *-resp-⟨ABox⟩ enode I′ A I′⊨A

  I-med : ∀ J → (J ⊨ T , A) → Mediated₀ I J
  I-med J (J⊨T , J⊨A) = lemma (I′-med J′ emp≲J′ (J⊨T , J′⊨A)) where

    J′ : Interp Σ (False ⊕ False ⊕ X)
    J′ = enode⁻¹ * J

    emp≲J′ : emp ≲ inode * J′
    emp≲J′ = emp-≲ (inode * J′)
    
    J′⊨A : J′ ⊨a ⟨ABox⟩ enode A
    J′⊨A = ⟨Abox⟩-resp-⊨ enode (λ x → ≈-refl ⌊ J ⌋) A J⊨A

    I≲J-impl-I′≲J′ : (I ≲ J) → (I′ ≲ J′)
    I≲J-impl-I′≲J′ I≲J = (≲⌊ I≲J ⌋ , i≲j) where

      i≲j : ∀ x → ⌊ J ⌋ ⊨ ≲-image ≲⌊ I≲J ⌋ (ind I′ x) ≈ ind J (enode⁻¹ x)
      i≲j (inode ())
      i≲j (bnode ())
      i≲j (enode x) = ≲-resp-ind I≲J x

    lemma : Mediated emp I′ J′ emp≲I′ emp≲J′ → Mediated₀ I J
    lemma (I≲J , _ , I≲J-uniq) = 
      ( (≲⌊ I≲J ⌋ , λ x → ≲-resp-ind I≲J (enode x))
      , λ I≲₁J I≲₂J x → I≲J-uniq 
          (I≲J-impl-I′≲J′ I≲₁J) (I≲J-impl-I′≲J′ I≲₂J) (λ ()) (λ ()) x)
