open import Data.Product using ( ∃ ; _×_ ; _,_ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Relation.Unary using ( _∈_ ; ∅ ; U ; _∪_ ; _∩_ ; ∁ )
open import Web.Semantic.DL.ABox.Signature using ( Signature ; tsig )
open import Web.Semantic.DL.Concept using ( Concept ; ⟨_⟩ ; ¬⟨_⟩ ; ⊤ ; ⊥ ; _⊓_ ; _⊔_ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1 ; >1 )
open import Web.Semantic.DL.Interp using ( Interp ; _⊨_≈_ ; _⊨_≉_ ; con ; con-≈ ; ≈-refl ; ≈-sym ; ≈-trans )
open import Web.Semantic.DL.Interp.Order using ( _≤_ ; ≤-resp-con ; ≤-resp-≈ )
open import Web.Semantic.DL.Role.Model using ( _⟦_⟧₂ ; ⟦⟧₂-resp-≈ ; ⟦⟧₂-resp-≤ )
open import Web.Semantic.Util using ( Subset ; tt ; _∘_ )

module Web.Semantic.DL.Concept.Model {Σ : Signature} {Δ : Set} where

_⟦_⟧₁ : ∀ (I : Interp Σ Δ) → Concept (tsig Σ) → Subset Δ
I ⟦ ⟨ c ⟩    ⟧₁ = con I c
I ⟦ ¬⟨ c ⟩   ⟧₁ = ∁ (con I c)
I ⟦ ⊤        ⟧₁ = U
I ⟦ ⊥        ⟧₁ = ∅
I ⟦ C ⊓ D    ⟧₁ = I ⟦ C ⟧₁ ∩ I ⟦ D ⟧₁
I ⟦ C ⊔ D    ⟧₁ = I ⟦ C ⟧₁ ∪ I ⟦ D ⟧₁
I ⟦ ∀[ R ] C ⟧₁ = λ x → ∀   y → ((x , y) ∈ I ⟦ R ⟧₂) → (y ∈ I ⟦ C ⟧₁)
I ⟦ ∃⟨ R ⟩ C ⟧₁ = λ x → ∃ λ y → ((x , y) ∈ I ⟦ R ⟧₂) × (y ∈ I ⟦ C ⟧₁)
I ⟦ ≤1 R     ⟧₁ = λ x → ∀ y z → ((x , y) ∈ I ⟦ R ⟧₂) → ((x , z) ∈ I ⟦ R ⟧₂) → (I ⊨ y ≈ z)
I ⟦ >1 R     ⟧₁ = λ x → ∃ λ y → ∃ λ z → ((x , y) ∈ I ⟦ R ⟧₂) × ((x , z) ∈ I ⟦ R ⟧₂) × (I ⊨ y ≉ z)

⟦⟧₁-resp-≈ : ∀ I C {x y} → (x ∈ I ⟦ C ⟧₁) → (I ⊨ x ≈ y) → (y ∈ I ⟦ C ⟧₁) 
⟦⟧₁-resp-≈ I ⟨ c ⟩      x∈⟦c⟧                           x≈y = 
  con-≈ I c x∈⟦c⟧ x≈y
⟦⟧₁-resp-≈ I ¬⟨ c ⟩     x∉⟦c⟧                           x≈y = 
  λ y∈⟦c⟧ → x∉⟦c⟧ (con-≈ I c y∈⟦c⟧ (≈-sym I x≈y))
⟦⟧₁-resp-≈ I ⊤          x∈⊤                             x≈y = 
  tt
⟦⟧₁-resp-≈ I (C ⊓ D)    (x∈⟦C⟧ , x∈⟦D⟧)                 x≈y =
  (⟦⟧₁-resp-≈ I C x∈⟦C⟧ x≈y , ⟦⟧₁-resp-≈ I D x∈⟦D⟧ x≈y)
⟦⟧₁-resp-≈ I (C ⊔ D)    (inj₁ x∈⟦C⟧)                    x≈y =
  inj₁ (⟦⟧₁-resp-≈ I C x∈⟦C⟧ x≈y)
⟦⟧₁-resp-≈ I (C ⊔ D)    (inj₂ x∈⟦D⟧)                    x≈y =
  inj₂ (⟦⟧₁-resp-≈ I D x∈⟦D⟧ x≈y)
⟦⟧₁-resp-≈ I (∀[ R ] C) x∈⟦∀RC⟧                         x≈y =
  λ z yz∈⟦R⟧ → x∈⟦∀RC⟧ z (⟦⟧₂-resp-≈ I R x≈y yz∈⟦R⟧ (≈-refl I))
⟦⟧₁-resp-≈ I (∃⟨ R ⟩ C) (z , xz∈⟦R⟧ , z∈⟦C⟧)            x≈y =
  (z , ⟦⟧₂-resp-≈ I R (≈-sym I x≈y) xz∈⟦R⟧ (≈-refl I) , z∈⟦C⟧)
⟦⟧₁-resp-≈ I (≤1 R)     x∈⟦≤1R⟧                         x≈y =
  λ w z yw∈⟦R⟧ yz∈⟦R⟧ → x∈⟦≤1R⟧ w z 
    (⟦⟧₂-resp-≈ I R x≈y yw∈⟦R⟧ (≈-refl I)) 
    (⟦⟧₂-resp-≈ I R x≈y yz∈⟦R⟧ (≈-refl I))
⟦⟧₁-resp-≈ I (>1 R)     (w , z , xw∈⟦R⟧ , xz∈⟦R⟧ , w≉z) x≈y =
  ( w , z 
  , ⟦⟧₂-resp-≈ I R (≈-sym I x≈y) xw∈⟦R⟧ (≈-refl I)
  , ⟦⟧₂-resp-≈ I R (≈-sym I x≈y) xz∈⟦R⟧ (≈-refl I)
  , w≉z)
⟦⟧₁-resp-≈ I ⊥          ()                              x≈y

⟦⟧₁-resp-≤≥ : ∀ {I J : Interp Σ Δ} → (I ≤ J) → (J ≤ I) → ∀ {x} C → (x ∈ I ⟦ C ⟧₁) → (x ∈ J ⟦ C ⟧₁)
⟦⟧₁-resp-≤≥ {I} {J} I≤J J≤I ⟨ c ⟩ x∈⟦c⟧ = 
  ≤-resp-con I≤J x∈⟦c⟧
⟦⟧₁-resp-≤≥ {I} {J} I≤J J≤I ¬⟨ c ⟩ x∉⟦c⟧ = 
  λ x∈⟦c⟧ → x∉⟦c⟧ (≤-resp-con J≤I x∈⟦c⟧)
⟦⟧₁-resp-≤≥ {I} {J} I≤J J≤I ⊤ _ = 
  tt
⟦⟧₁-resp-≤≥ {I} {J} I≤J J≤I ⊥ ()
⟦⟧₁-resp-≤≥ {I} {J} I≤J J≤I (C ⊓ D) (x∈⟦C⟧ , x∈⟦D⟧) = 
  (⟦⟧₁-resp-≤≥ I≤J J≤I C x∈⟦C⟧ , ⟦⟧₁-resp-≤≥ I≤J J≤I D x∈⟦D⟧)
⟦⟧₁-resp-≤≥ {I} {J} I≤J J≤I (C ⊔ D) (inj₁ x∈⟦C⟧) = 
  inj₁ (⟦⟧₁-resp-≤≥ I≤J J≤I C x∈⟦C⟧)
⟦⟧₁-resp-≤≥ {I} {J} I≤J J≤I (C ⊔ D) (inj₂ x∈⟦D⟧) = 
  inj₂ (⟦⟧₁-resp-≤≥ I≤J J≤I D x∈⟦D⟧)
⟦⟧₁-resp-≤≥ {I} {J} I≤J J≤I (∀[ R ] C) x∈⟦∀RC⟧ = 
  λ y xy∈⟦R⟧ → (⟦⟧₁-resp-≤≥ I≤J J≤I C (x∈⟦∀RC⟧ y (⟦⟧₂-resp-≤ J≤I R xy∈⟦R⟧)))
⟦⟧₁-resp-≤≥ {I} {J} I≤J J≤I (∃⟨ R ⟩ C) (y , xy∈⟦R⟧ , y∈⟦C⟧) = 
  (y , ⟦⟧₂-resp-≤ I≤J R xy∈⟦R⟧ , ⟦⟧₁-resp-≤≥ I≤J J≤I C y∈⟦C⟧)
⟦⟧₁-resp-≤≥ {I} {J} I≤J J≤I (≤1 R) x∈⟦≤1R⟧ = 
  λ y z xy∈⟦R⟧ xz∈⟦R⟧ → 
    ≤-resp-≈ I≤J (x∈⟦≤1R⟧ y z (⟦⟧₂-resp-≤ J≤I R xy∈⟦R⟧) (⟦⟧₂-resp-≤ J≤I R xz∈⟦R⟧))
⟦⟧₁-resp-≤≥ {I} {J} I≤J J≤I (>1 R) (y , z , xy∈⟦R⟧ , xz∈⟦R⟧ , y≉z) = 
  (y , z , ⟦⟧₂-resp-≤ I≤J R xy∈⟦R⟧ , ⟦⟧₂-resp-≤ I≤J R xz∈⟦R⟧ , y≉z ∘ ≤-resp-≈ J≤I)
