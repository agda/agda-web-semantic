open import Data.Product using ( ∃ ; _×_ ; _,_ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Relation.Unary using ( _∈_ ; _∉_ ; ∅ ; U ; _∪_ ; _∩_ ; ∁ )
open import Web.Semantic.DL.Concept using ( Concept ; ⟨_⟩ ; ¬⟨_⟩ ; ⊤ ; ⊥ ; _⊓_ ; _⊔_ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1 ; >1 ; neg )
open import Web.Semantic.DL.Role.Model using ( _⟦_⟧₂ ; ⟦⟧₂-resp-≈ ; ⟦⟧₂-resp-≲ ; ⟦⟧₂-galois )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox.Interp using ( Interp ; Δ ; _⊨_≈_ ; _⊨_≉_ ; con ; con-≈ ; ≈-refl ; ≈-sym ; ≈-trans )
open import Web.Semantic.DL.TBox.Interp.Morphism using ( _≲_ ; _≃_ ; ≲-resp-con ; ≲-resp-≈ ; ≃-impl-≲ ; ≃-impl-≳ ; ≃-iso ; ≃-iso⁻¹ ; ≃-image ; ≃-image⁻¹ ; ≃-refl-≈ ; ≃-sym )
open import Web.Semantic.Util using ( Subset ; tt ; _∘_ )

module Web.Semantic.DL.Concept.Model {Σ : Signature} where

_⟦_⟧₁ : ∀ (I : Interp Σ) → Concept Σ → Subset (Δ I)
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

mutual

  ⟦⟧₁-refl-≃ : ∀ {I J : Interp Σ} → (I≃J : I ≃ J) → ∀ {x} C → (≃-image⁻¹ I≃J x ∈ I ⟦ C ⟧₁) → (x ∈ J ⟦ C ⟧₁)
  ⟦⟧₁-refl-≃ {I} {J} I≃J {x} C x∈⟦C⟧ = ⟦⟧₁-resp-≈ J C (⟦⟧₁-resp-≃ I≃J C x∈⟦C⟧) (≃-iso⁻¹ I≃J x)

  ⟦⟧₁-resp-≃ : ∀ {I J : Interp Σ} → (I≃J : I ≃ J) → ∀ {x} C → (x ∈ I ⟦ C ⟧₁) → (≃-image I≃J x ∈ J ⟦ C ⟧₁)
  ⟦⟧₁-resp-≃ {I} {J} I≃J ⟨ c ⟩ x∈⟦c⟧ = 
    ≲-resp-con (≃-impl-≲ I≃J) x∈⟦c⟧
  ⟦⟧₁-resp-≃ {I} {J} I≃J {x} ¬⟨ c ⟩ x∉⟦c⟧ = 
    λ x∈⟦c⟧ → x∉⟦c⟧ (con-≈ I c (≲-resp-con (≃-impl-≳ I≃J) x∈⟦c⟧) (≃-iso I≃J x))
  ⟦⟧₁-resp-≃ {I} {J} I≃J ⊤ _ = 
    tt
  ⟦⟧₁-resp-≃ {I} {J} I≃J ⊥ ()
  ⟦⟧₁-resp-≃ {I} {J} I≃J (C ⊓ D) (x∈⟦C⟧ , x∈⟦D⟧) = 
    (⟦⟧₁-resp-≃ I≃J C x∈⟦C⟧ , ⟦⟧₁-resp-≃ I≃J D x∈⟦D⟧)
  ⟦⟧₁-resp-≃ {I} {J} I≃J (C ⊔ D) (inj₁ x∈⟦C⟧) = 
    inj₁ (⟦⟧₁-resp-≃ I≃J C x∈⟦C⟧)
  ⟦⟧₁-resp-≃ {I} {J} I≃J (C ⊔ D) (inj₂ x∈⟦D⟧) = 
    inj₂ (⟦⟧₁-resp-≃ I≃J D x∈⟦D⟧)
  ⟦⟧₁-resp-≃ {I} {J} I≃J (∀[ R ] C) x∈⟦∀RC⟧ = 
    λ y xy∈⟦R⟧ → ⟦⟧₁-refl-≃ I≃J C 
      (x∈⟦∀RC⟧ (≃-image⁻¹ I≃J y) (⟦⟧₂-galois (≃-sym I≃J) R xy∈⟦R⟧))
  ⟦⟧₁-resp-≃ {I} {J} I≃J (∃⟨ R ⟩ C) (y , xy∈⟦R⟧ , y∈⟦C⟧) = 
    ( ≃-image I≃J y 
    , ⟦⟧₂-resp-≲ (≃-impl-≲ I≃J) R xy∈⟦R⟧ 
    , ⟦⟧₁-resp-≃ I≃J C y∈⟦C⟧ )
  ⟦⟧₁-resp-≃ {I} {J} I≃J (≤1 R) x∈⟦≤1R⟧ = 
    λ y z xy∈⟦R⟧ xz∈⟦R⟧ → ≃-refl-≈ I≃J 
      (x∈⟦≤1R⟧ (≃-image⁻¹ I≃J y) (≃-image⁻¹ I≃J z) 
      (⟦⟧₂-galois (≃-sym I≃J) R xy∈⟦R⟧) (⟦⟧₂-galois (≃-sym I≃J) R xz∈⟦R⟧))
  ⟦⟧₁-resp-≃ {I} {J} I≃J (>1 R) (y , z , xy∈⟦R⟧ , xz∈⟦R⟧ , y≉z) = 
    ( ≃-image I≃J y , ≃-image I≃J z 
    , ⟦⟧₂-resp-≲ (≃-impl-≲ I≃J) R xy∈⟦R⟧
    , ⟦⟧₂-resp-≲ (≃-impl-≲ I≃J) R xz∈⟦R⟧
    , y≉z ∘ ≃-refl-≈ (≃-sym I≃J) )

neg-sound : ∀ I {x} C → (x ∈ I ⟦ neg C ⟧₁) → (x ∉ I ⟦ C ⟧₁)
neg-sound I ⟨ c ⟩ x∉⟦c⟧ x∈⟦c⟧ = x∉⟦c⟧ x∈⟦c⟧
neg-sound I ¬⟨ c ⟩ x∈⟦c⟧ x∉⟦c⟧ = x∉⟦c⟧ x∈⟦c⟧
neg-sound I ⊤ () _
neg-sound I ⊥ _ ()
neg-sound I (C ⊓ D) (inj₁ x∈⟦¬C⟧) (x∈⟦C⟧ , x∈⟦D⟧) = neg-sound I C x∈⟦¬C⟧ x∈⟦C⟧
neg-sound I (C ⊓ D) (inj₂ x∈⟦¬D⟧) (x∈⟦C⟧ , x∈⟦D⟧) = neg-sound I D x∈⟦¬D⟧ x∈⟦D⟧
neg-sound I (C ⊔ D) (x∈⟦¬C⟧ , x∈⟦¬D⟧) (inj₁ x∈⟦C⟧) = neg-sound I C x∈⟦¬C⟧ x∈⟦C⟧
neg-sound I (C ⊔ D) (x∈⟦¬C⟧ , x∈⟦¬D⟧) (inj₂ x∈⟦D⟧) = neg-sound I D x∈⟦¬D⟧ x∈⟦D⟧
neg-sound I (∀[ R ] C) (y , xy∈⟦R⟧ , y∈⟦¬C⟧) x∈⟦∀RC⟧ = neg-sound I C y∈⟦¬C⟧ (x∈⟦∀RC⟧ y xy∈⟦R⟧)
neg-sound I (∃⟨ R ⟩ C) x∈⟦∀R¬C⟧ (y , xy∈⟦R⟧ , y∈⟦C⟧) = neg-sound I C (x∈⟦∀R¬C⟧ y xy∈⟦R⟧) y∈⟦C⟧
neg-sound I (≤1 R) (y , z , xy∈⟦R⟧ , xz∈⟦R⟧ , y≉z) x∈⟦≤1R⟧ = y≉z (x∈⟦≤1R⟧ y z xy∈⟦R⟧ xz∈⟦R⟧)
neg-sound I (>1 R) x∈⟦≤1R⟧ (y , z , xy∈⟦R⟧ , xz∈⟦R⟧ , y≉z) = y≉z (x∈⟦≤1R⟧ y z xy∈⟦R⟧ xz∈⟦R⟧)
