open import Data.Product using ( _,_ ; proj₁ ; proj₂ )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox ; _,_ ; ⟨ABox⟩ )
open import Web.Semantic.DL.ABox.Interp using ( Interp ; _,_ ; ⌊_⌋ ; ind ; _*_ )
open import Web.Semantic.DL.ABox.Interp.Morphism using 
  ( _≲_ ; _,_ ; ≲⌊_⌋ ; ≲-resp-ind ; _**_ ; ≡³-impl-≈ ; ≡³-impl-≲ )
open import Web.Semantic.DL.ABox.Model using ( _⊨a_ ; ⟨ABox⟩-resp-⊨ ; ⊨a-resp-≲ ; *-resp-⟨ABox⟩ )
open import Web.Semantic.DL.Category.Morphism using ( _⇒_ ; _,_ ; BN ; impl ; impl✓ )
open import Web.Semantic.DL.Category.Object using ( Object ; _,_ ; IN ; fin ; iface )
open import Web.Semantic.DL.Integrity using 
  ( _⊕_⊨_ ; Unique ; Mediated ; Mediator ; Initial 
  ; _,_ ; extension ; ext-init ; ext-⊨ ; ext✓ ; init-≲ )
open import Web.Semantic.DL.KB using ( _,_ )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox ; _,_ )
open import Web.Semantic.DL.TBox.Interp using ( _⊨_≈_ ; ≈-refl ; ≈-sym ; ≈-trans )
open import Web.Semantic.DL.TBox.Model using ( _⊨t_ )
open import Web.Semantic.DL.TBox.Interp.Morphism using 
  ( ≲-image ; ≲-resp-≈ ; ≲-trans ) renaming ( _≲_ to _≲′_ )
open import Web.Semantic.Util using 
  ( _∘_ ; ⊎-resp-Fin ; _⊕_⊕_ ; inode ; bnode ; enode ; ⊕-inj₁ ; ⊕-inj₂ ; shuffle )

module Web.Semantic.DL.Category.Tensor {Σ : Signature} where

_&_ : ∀ {X₁ X₂} → ABox Σ X₁ → ABox Σ X₂ → ABox Σ (X₁ ⊎ X₂)
A₁ & A₂ = (⟨ABox⟩ inj₁ A₁ , ⟨ABox⟩ inj₂ A₂)

_⊗_ : ∀ {S T : TBox Σ} → Object S T → Object S T →  Object S T
A₁ ⊗ A₂ = 
  ( (IN A₁ ⊎ IN A₂) 
  , ⊎-resp-Fin (fin A₁) (fin A₂)
  , iface A₁ & iface A₂ )

_⟨&⟩_ : ∀ {V₁ V₂ X₁ X₂ Y₁ Y₂} → 
  ABox Σ (X₁ ⊕ V₁ ⊕ Y₁) → ABox Σ (X₂ ⊕ V₂ ⊕ Y₂) → 
    ABox Σ ((X₁ ⊎ X₂) ⊕ (V₁ ⊎ V₂) ⊕ (Y₁ ⊎ Y₂))
F₁ ⟨&⟩ F₂ = (⟨ABox⟩ ⊕-inj₁ F₁ , ⟨ABox⟩ ⊕-inj₂ F₂)

go₂ : ∀ {V₁ X₁ X₂ Y₁} → (I : Interp Σ (X₁ ⊎ X₂)) →
  (J₁ : Interp Σ (X₁ ⊕ V₁ ⊕ Y₁)) → (⌊ I ⌋ ≲′ ⌊ J₁ ⌋) →
    Interp Σ X₂
go₂ I J₁ I≲J = (⌊ J₁ ⌋ , ≲-image I≲J ∘ ind I ∘ inj₂)

go₂-≳ : ∀ {V₁ X₁ X₂ Y₁} → (I : Interp Σ (X₁ ⊎ X₂)) →
  (J₁ : Interp Σ (X₁ ⊕ V₁ ⊕ Y₁)) → (I≲J : ⌊ I ⌋ ≲′ ⌊ J₁ ⌋) →
    (inj₂ * I ≲ go₂ I J₁ I≲J)
go₂-≳ I (J , j₁) I≲J = (I≲J , λ x → ≈-refl J)

go₂-≲ : ∀ {V₁ V₂ X₁ X₂ Y₁ Y₂} → (I : Interp Σ (X₁ ⊎ X₂)) →
  (J₁ : Interp Σ (X₁ ⊕ V₁ ⊕ Y₁)) → 
    (L : Interp Σ ((X₁ ⊎ X₂) ⊕ (V₁ ⊎ V₂) ⊕ (Y₁ ⊎ Y₂))) →
      (I₁≲J₁ : inj₁ * I ≲ inode * J₁) → (I≲L : I ≲ inode * L) →
        (Mediated (inj₁ * I) J₁ (⊕-inj₁ * L) I₁≲J₁ (inj₁ ** I≲L)) → 
          (go₂ I J₁ ≲⌊ I₁≲J₁ ⌋ ≲ inode * (⊕-inj₂ * L))
go₂-≲ (I , i) (J , j₁) (L , l) (I≲J , i₁≲j₁) (I≲L , i≲l) 
  ((J≲L , j₁≲l₁) , I≲L≋I≲J≲L , J₁≲L₁-uniq) = 
    (J≲L , λ x → ≈-trans L (≈-sym L (I≲L≋I≲J≲L (i (inj₂ x)))) (i≲l (inj₂ x)))

par : ∀ {V₁ V₂ X₁ X₂ Y₁ Y₂} → (J₁ : Interp Σ (X₁ ⊕ V₁ ⊕ Y₁)) →
  (K₂ : Interp Σ (X₂ ⊕ V₂ ⊕ Y₂)) → (⌊ J₁ ⌋ ≲′ ⌊ K₂ ⌋) → 
    Interp Σ ((X₁ ⊎ X₂) ⊕ (V₁ ⊎ V₂) ⊕ (Y₁ ⊎ Y₂))
par J₁ K₂ J≲K = 
  (⌊ K₂ ⌋ , shuffle (≲-image J≲K ∘ ind J₁) (ind K₂))

par-inj₁ : ∀ {V₁ V₂ X₁ X₂ Y₁ Y₂} → (J₁ : Interp Σ (X₁ ⊕ V₁ ⊕ Y₁)) →
  (K₂ : Interp Σ (X₂ ⊕ V₂ ⊕ Y₂)) → (J≲K : ⌊ J₁ ⌋ ≲′ ⌊ K₂ ⌋) →
    (J₁ ≲ ⊕-inj₁ * par J₁ K₂ J≲K)
par-inj₁ (J , j₁) (K , k₂) J≲K = 
  ( J≲K 
  , ≡³-impl-≈ K
      (≲-image J≲K ∘ j₁)
      (shuffle (≲-image J≲K ∘ j₁) k₂ ∘ ⊕-inj₁)
      refl )

par-inj₂ : ∀ {V₁ V₂ X₁ X₂ Y₁ Y₂} → (J₁ : Interp Σ (X₁ ⊕ V₁ ⊕ Y₁)) →
  (K₂ : Interp Σ (X₂ ⊕ V₂ ⊕ Y₂)) → (J≲K : ⌊ J₁ ⌋ ≲′ ⌊ K₂ ⌋) →
    (K₂ ≲ ⊕-inj₂ * par J₁ K₂ J≲K)
par-inj₂ (J , j₁) (K , k₂) J≲K = 
  ≡³-impl-≲ (K , k₂) (shuffle (≲-image J≲K ∘ j₁) k₂ ∘ ⊕-inj₂) refl

par-exp : ∀ {V₁ V₂ X₁ X₂ Y₁ Y₂} → (J₁ : Interp Σ (X₁ ⊕ V₁ ⊕ Y₁)) →
  (K₂ : Interp Σ (X₂ ⊕ V₂ ⊕ Y₂)) → (J≲K : ⌊ J₁ ⌋ ≲′ ⌊ K₂ ⌋) →
    (T : TBox Σ) → (B₁ : ABox Σ Y₁) → (B₂ : ABox Σ Y₂) → 
      (enode * J₁ ⊨ T , B₁) → (enode * K₂ ⊨ T , B₂) →
        (enode * (par J₁ K₂ J≲K) ⊨ T , (B₁ & B₂))
par-exp J₁ K₂ J≲K T B₁ B₂ (J⊨T , J₁⊨B₁) (K⊨T , K₂⊨B₂) = 
  ( K⊨T
  , ⟨ABox⟩-resp-⊨ inj₁ (λ y → ≈-refl ⌊ K₂ ⌋) B₁
      (⊨a-resp-≲ (enode ** par-inj₁ J₁ K₂ J≲K) B₁ J₁⊨B₁)
  , ⟨ABox⟩-resp-⊨ inj₂ (λ y → ≈-refl ⌊ K₂ ⌋) B₂ K₂⊨B₂)

par-≳ : ∀ {V₁ V₂ X₁ X₂ Y₁ Y₂} → (I : Interp Σ (X₁ ⊎ X₂)) →
  (J₁ : Interp Σ (X₁ ⊕ V₁ ⊕ Y₁)) → (K₂ : Interp Σ (X₂ ⊕ V₂ ⊕ Y₂)) → 
    (I₁≲J₁ : inj₁ * I ≲ inode * J₁) → 
      (J₂≲K₂ : go₂ I J₁ ≲⌊ I₁≲J₁ ⌋ ≲ inode * K₂) →
        (I ≲ inode * par J₁ K₂ ≲⌊ J₂≲K₂ ⌋)
par-≳ I J₁ K₂ (I≲J , i₁≲j₁) (J≲K , j₂≲k₂) =
  ( ≲-trans I≲J J≲K , lemma ) where

  lemma : ∀ x → ⌊ K₂ ⌋ ⊨
    ≲-image J≲K (≲-image I≲J (ind I x)) ≈
      shuffle (≲-image J≲K ∘ ind J₁) (ind K₂) (inode x)
  lemma (inj₁ x) = ≲-resp-≈ J≲K (i₁≲j₁ x)
  lemma (inj₂ x) = j₂≲k₂ x

par-impl : ∀ {V₁ V₂ X₁ X₂ Y₁ Y₂} → (J₁ : Interp Σ (X₁ ⊕ V₁ ⊕ Y₁)) →
  (K₂ : Interp Σ (X₂ ⊕ V₂ ⊕ Y₂)) → (J≲K : ⌊ J₁ ⌋ ≲′ ⌊ K₂ ⌋) →
    (F₁ : ABox Σ (X₁ ⊕ V₁ ⊕ Y₁)) → (F₂ : ABox Σ (X₂ ⊕ V₂ ⊕ Y₂)) →
      (J₁ ⊨a F₁) → (K₂ ⊨a F₂) →
        (par J₁ K₂ J≲K ⊨a F₁ ⟨&⟩ F₂)
par-impl J₁ K₂ J≲K F₁ F₂ J₁⊨F₁ K₂⊨F₂ = 
  ( ⟨ABox⟩-resp-⊨ ⊕-inj₁ (λ x → ≈-refl ⌊ K₂ ⌋) F₁ 
      (⊨a-resp-≲ (par-inj₁ J₁ K₂ J≲K) F₁ J₁⊨F₁)
  , ⟨ABox⟩-resp-⊨ ⊕-inj₂ (λ x → ≈-refl ⌊ K₂ ⌋) F₂ 
      (⊨a-resp-≲ (par-inj₂ J₁ K₂ J≲K) F₂ K₂⊨F₂) )

par-mediated : ∀ {V₁ V₂ X₁ X₂ Y₁ Y₂} → (I : Interp Σ (X₁ ⊎ X₂)) →
  (J₁ : Interp Σ (X₁ ⊕ V₁ ⊕ Y₁)) → (K₂ : Interp Σ (X₂ ⊕ V₂ ⊕ Y₂)) → 
    (L : Interp Σ ((X₁ ⊎ X₂) ⊕ (V₁ ⊎ V₂) ⊕ (Y₁ ⊎ Y₂))) → 
      (I₁≲J₁ : inj₁ * I ≲ inode * J₁) → (I≲L : I ≲ inode * L) → 
        (J₂≲K₂ : go₂ I J₁ ≲⌊ I₁≲J₁ ⌋ ≲ inode * K₂) → 
          (m : Mediated (inj₁ * I) J₁ (⊕-inj₁ * L) I₁≲J₁ (inj₁ ** I≲L)) → 
            (Mediated (go₂ I J₁ ≲⌊ I₁≲J₁ ⌋) K₂ (⊕-inj₂ * L) J₂≲K₂ (go₂-≲ I J₁ L I₁≲J₁ I≲L m)) → 
              (Mediated I (par J₁ K₂ ≲⌊ J₂≲K₂ ⌋) L (par-≳ I J₁ K₂ I₁≲J₁ J₂≲K₂) I≲L)
par-mediated (I , i) (J , j₁) (K , k₂) (L , l) (I≲J , i₁≲j₁) (I≲L , i≲l) (J≲K , j₂≲k₂) 
  ((J≲L , j₁≲l₁) , I≲L≋I≲J≲L , J₁≲L₁-uniq) ((K≲L , k₂≲l₂) , J≲L≋J≲K≲L , K₂≲L₂-uniq) = 
    ((K≲L , k≲l) , I≲L≋I≲K≲L , K≲L-uniq) where

  k = shuffle (≲-image J≲K ∘ j₁) k₂

  I≲K : I ≲′ K
  I≲K = ≲-trans I≲J J≲K

  i≲k : ∀ x → K ⊨ ≲-image I≲K (i x) ≈ k (inode x)
  i≲k = ≲-resp-ind (par-≳ (I , i) (J , j₁) (K , k₂) (I≲J , i₁≲j₁) (J≲K , j₂≲k₂))

  k≲l : ∀ x → L ⊨ ≲-image K≲L (k x) ≈ l x
  k≲l (inode (inj₁ x)) = ≈-trans L (≈-sym L (J≲L≋J≲K≲L (j₁ (inode x)))) (j₁≲l₁ (inode x))
  k≲l (inode (inj₂ x)) = k₂≲l₂ (inode x)
  k≲l (bnode (inj₁ v)) = ≈-trans L (≈-sym L (J≲L≋J≲K≲L (j₁ (bnode v)))) (j₁≲l₁ (bnode v))
  k≲l (bnode (inj₂ v)) = k₂≲l₂ (bnode v)
  k≲l (enode (inj₁ y)) = ≈-trans L (≈-sym L (J≲L≋J≲K≲L (j₁ (enode y)))) (j₁≲l₁ (enode y))
  k≲l (enode (inj₂ y)) = k₂≲l₂ (enode y)

  I≲L≋I≲K≲L : ∀ x → L ⊨ ≲-image I≲L x ≈ ≲-image K≲L (≲-image I≲K x)
  I≲L≋I≲K≲L x = ≈-trans L (I≲L≋I≲J≲L x) (J≲L≋J≲K≲L (≲-image I≲J x))

  lemma₁ : ∀ (K≲L : (K , k) ≲ (L , l)) x → (L ⊨ ≲-image ≲⌊ K≲L ⌋ (≲-image J≲K (j₁ x)) ≈ l (⊕-inj₁ x))
  lemma₁ (K≲L' , k≲l) (inode x) = k≲l (inode (inj₁ x))
  lemma₁ (K≲L' , k≲l) (bnode v) = k≲l (bnode (inj₁ v))
  lemma₁ (K≲L' , k≲l) (enode y) = k≲l (enode (inj₁ y))

  lemma₂ : ∀ (K≲L : (K , k) ≲ (L , l)) x → (L ⊨ ≲-image ≲⌊ K≲L ⌋ (k₂ x) ≈ l (⊕-inj₂ x))
  lemma₂ (K≲L , k≲l) (inode x) = k≲l (inode (inj₂ x))
  lemma₂ (K≲L , k≲l) (bnode v) = k≲l (bnode (inj₂ v))
  lemma₂ (K≲L , k≲l) (enode y) = k≲l (enode (inj₂ y))

  K≲L-uniq : Unique (I , i) (K , k) (L , l) (I≲K , i≲k) (I≲L , i≲l)
  K≲L-uniq (K≲₁L , k≲₁l) (K≲₂L , k≲₂l) I≲L≋I≲K≲₁L I≲L≋I≲K≲₂L = 
    K₂≲L₂-uniq (K≲₁L , lemma₂ (K≲₁L , k≲₁l)) (K≲₂L , lemma₂ (K≲₂L , k≲₂l))
      (J₁≲L₁-uniq (J≲L , j₁≲l₁) (≲-trans J≲K K≲₁L , lemma₁ (K≲₁L , k≲₁l)) I≲L≋I≲J≲L I≲L≋I≲K≲₁L)
      (J₁≲L₁-uniq (J≲L , j₁≲l₁) (≲-trans J≲K K≲₂L , lemma₁ (K≲₂L , k≲₂l)) I≲L≋I≲J≲L I≲L≋I≲K≲₂L)

par-mediator : ∀ {V₁ V₂ X₁ X₂ Y₁ Y₂} → (I : Interp Σ (X₁ ⊎ X₂)) →
  (J₁ : Interp Σ (X₁ ⊕ V₁ ⊕ Y₁)) → (K₂ : Interp Σ (X₂ ⊕ V₂ ⊕ Y₂)) → 
    (I₁≲J₁ : inj₁ * I ≲ inode * J₁) → 
      (J₂≲K₂ : go₂ I J₁ ≲⌊ I₁≲J₁ ⌋ ≲ inode * K₂) → (S : TBox Σ) → 
        (F₁ : ABox Σ (X₁ ⊕ V₁ ⊕ Y₁)) → (F₂ : ABox Σ (X₂ ⊕ V₂ ⊕ Y₂)) →
          (Mediator (inj₁ * I) J₁ I₁≲J₁ (S , F₁)) →
            (Mediator (go₂ I J₁ ≲⌊ I₁≲J₁ ⌋) K₂ J₂≲K₂ (S , F₂)) →
              (Mediator I (par J₁ K₂ ≲⌊ J₂≲K₂ ⌋) 
                (par-≳ I J₁ K₂ I₁≲J₁ J₂≲K₂) (S , (F₁ ⟨&⟩ F₂)))
par-mediator I J₁ K₂ I₁≲J₁ J₂≲K₂ S F₁ F₂ J₁-med K₂-med L I≲L (L⊨S , L⊨F₁ , L⊨F₂) = 
  par-mediated I J₁ K₂ L I₁≲J₁ I≲L J₂≲K₂ I₁≲J₁≲L₁-med J₂≲K₂≲L₂-med where

  I₁≲J₁≲L₁-med : Mediated (inj₁ * I) J₁ (⊕-inj₁ * L) I₁≲J₁ (inj₁ ** I≲L)
  I₁≲J₁≲L₁-med = J₁-med (⊕-inj₁ * L) (inj₁ ** I≲L) (L⊨S , *-resp-⟨ABox⟩ ⊕-inj₁ L F₁ L⊨F₁)

  J₂≲K₂≲L₂-med : Mediated (go₂ I J₁ ≲⌊ I₁≲J₁ ⌋) K₂ (⊕-inj₂ * L) J₂≲K₂ (go₂-≲ I J₁ L I₁≲J₁ I≲L I₁≲J₁≲L₁-med)
  J₂≲K₂≲L₂-med = K₂-med (⊕-inj₂ * L) (go₂-≲ I J₁ L I₁≲J₁ I≲L I₁≲J₁≲L₁-med) (L⊨S , *-resp-⟨ABox⟩ ⊕-inj₂ L F₂ L⊨F₂)

par-init : ∀ {V₁ V₂ X₁ X₂ Y₁ Y₂} → (I : Interp Σ (X₁ ⊎ X₂)) →
  (J₁ : Interp Σ (X₁ ⊕ V₁ ⊕ Y₁)) → (K₂ : Interp Σ (X₂ ⊕ V₂ ⊕ Y₂)) → 
    (S : TBox Σ) → (F₁ : ABox Σ (X₁ ⊕ V₁ ⊕ Y₁)) → (F₂ : ABox Σ (X₂ ⊕ V₂ ⊕ Y₂)) →
      (J₁-init : J₁ ∈ Initial (inj₁ * I) (S , F₁)) → 
        (K₂-init : K₂ ∈ Initial (go₂ I J₁ ≲⌊ init-≲ J₁-init ⌋) (S , F₂)) →
          (par J₁ K₂ ≲⌊ init-≲ K₂-init ⌋ ∈ 
            Initial I (S , (F₁ ⟨&⟩ F₂)))
par-init I J₁ K₂ S F₁ F₂
  (I₁≲J₁ , (J⊨S , J₁⊨F₁) , J₁-med) (J₂≲K₂ , (K⊨S , K₂⊨F₂) , K₂-med) = 
    ( par-≳ I J₁ K₂ I₁≲J₁ J₂≲K₂
    , (K⊨S , par-impl J₁ K₂ ≲⌊ J₂≲K₂ ⌋ F₁ F₂ J₁⊨F₁ K₂⊨F₂)
    , par-mediator I J₁ K₂ I₁≲J₁ J₂≲K₂ S F₁ F₂ J₁-med K₂-med )

tensor-⊨ : ∀ {V₁ V₂ X₁ X₂ Y₁ Y₂} → (S T : TBox Σ) →
  (A₁ : ABox Σ X₁) → (A₂ : ABox Σ X₂) → (B₁ : ABox Σ Y₁) → (B₂ : ABox Σ Y₂) →
    (F₁ : ABox Σ (X₁ ⊕ V₁ ⊕ Y₁)) (F₂ : ABox Σ (X₂ ⊕ V₂ ⊕ Y₂)) →
      (∀ I → (I ⊨ (S , T) , A₁) → (I ⊕ S , F₁ ⊨ T , B₁)) →
        (∀ I → (I ⊨ (S , T) , A₂) → (I ⊕ S , F₂ ⊨ T , B₂)) →
          (∀ I → (I ⊨ (S , T) , (A₁ & A₂)) → 
            (I ⊕ S , F₁ ⟨&⟩ F₂ ⊨ T , (B₁ & B₂)))
tensor-⊨ {V₁} {V₂} {X₁} {X₂} {Y₁} {Y₂} 
  S T A₁ A₂ B₁ B₂ F₁ F₂ F₁✓ F₂✓ I (I⊨ST , (I⊨A₁ , I⊨A₂)) = 
    ( par J₁ K₂ ≲⌊ J₂≲K₂ ⌋
    , par-init I J₁ K₂ S F₁ F₂ J₁-init K₂-init
    , par-exp J₁ K₂ ≲⌊ J₂≲K₂ ⌋ T B₁ B₂ 
        (ext-⊨ I₁⊕SF₁⊨TB₁) (ext-⊨ J₂⊕SF₂⊨TB₂) ) where

  I₁ : Interp Σ X₁
  I₁ = inj₁ * I

  I₂ : Interp Σ X₂
  I₂ = inj₂ * I

  I₁⊨A₁ : I₁ ⊨a A₁
  I₁⊨A₁ = *-resp-⟨ABox⟩ inj₁ I A₁ I⊨A₁

  I₂⊨A₂ : I₂ ⊨a A₂
  I₂⊨A₂ = *-resp-⟨ABox⟩ inj₂ I A₂ I⊨A₂

  I₁⊕SF₁⊨TB₁ : I₁ ⊕ S , F₁ ⊨ T , B₁
  I₁⊕SF₁⊨TB₁ = F₁✓ I₁ (I⊨ST , I₁⊨A₁)
  
  J₁ : Interp Σ (X₁ ⊕ V₁ ⊕ Y₁)
  J₁ = extension I₁⊕SF₁⊨TB₁

  J₁-init : J₁ ∈ Initial I₁ (S , F₁)
  J₁-init = ext-init I₁⊕SF₁⊨TB₁

  I₁≲J₁ : I₁ ≲ inode * J₁
  I₁≲J₁ = init-≲ J₁-init

  J₂ : Interp Σ X₂
  J₂ = go₂ I J₁ ≲⌊ I₁≲J₁ ⌋

  I₂≲J₂ : I₂ ≲ J₂
  I₂≲J₂ = go₂-≳ I J₁ ≲⌊ I₁≲J₁ ⌋

  J⊨ST : ⌊ J₂ ⌋ ⊨t (S , T)
  J⊨ST = proj₁ (ext✓ I₁⊕SF₁⊨TB₁)

  J₂⊨A₂ : J₂ ⊨a A₂
  J₂⊨A₂ = ⊨a-resp-≲ I₂≲J₂ A₂ I₂⊨A₂
  
  J₂⊕SF₂⊨TB₂ : J₂ ⊕ S , F₂ ⊨ T , B₂
  J₂⊕SF₂⊨TB₂ = F₂✓ J₂ (J⊨ST , J₂⊨A₂)

  K₂ : Interp Σ (X₂ ⊕ V₂ ⊕ Y₂)
  K₂ = extension J₂⊕SF₂⊨TB₂

  K₂-init : K₂ ∈ Initial J₂ (S , F₂)
  K₂-init = ext-init J₂⊕SF₂⊨TB₂

  J₂≲K₂ : J₂ ≲ inode * K₂
  J₂≲K₂ = init-≲ K₂-init

_⟨⊗⟩_ : ∀ {S T : TBox Σ} {A₁ A₂ B₁ B₂ : Object S T} → 
  (A₁ ⇒ B₁) → (A₂ ⇒ B₂) → ((A₁ ⊗ A₂) ⇒ (B₁ ⊗ B₂))
_⟨⊗⟩_ {S} {T} {A₁} {A₂} {B₁} {B₂} F₁ F₂  = 
  ( (BN F₁ ⊎ BN F₂)
  , (impl F₁ ⟨&⟩ impl F₂)
  , tensor-⊨ S T (iface A₁) (iface A₂) (iface B₁) (iface B₂)
      (impl F₁) (impl F₂) (impl✓ F₁) (impl✓ F₂) )
