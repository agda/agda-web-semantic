open import Data.Product using ( ∃ ; _×_ ; _,_ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Relation.Nullary using ( ¬_ )
open import Relation.Unary using ( _∈_ ; _⊆_ ; ∅ ; U ; _∪_ ; _∩_ ; ∁ )
open import Web.Semantic.DL.Interp using
  ( Interp ; Δ ; _⊨_≈_ ; _⊨_≉_ ; ≈-refl ; ≈-sym
  ; con ; rol ; con-≈ ; rol-≈ )
open import Web.Semantic.DL.Signature using ( Signature ; CN ; RN )
open import Web.Semantic.DL.TBox using
  ( Concept ; Role ; TBox ; Axioms
  ; ⟨_⟩ ; ¬⟨_⟩ ; ⟨_⟩⁻¹ ; ⊤ ; ⊥ ; _⊓_ ; _⊔_ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1 ; >1
  ; ε ; _,_ ;_⊑₁_ ; _⊑₂_ )
open import Web.Semantic.Util using ( True ; Subset ; _⁻¹ ; tt )

module Web.Semantic.DL.TBox.Model {Σ : Signature} {X : Set} where

infixr 2 _⊨t_

_⟦_⟧₂ : ∀ I → Role Σ → Subset (Δ I × Δ I)
I ⟦ ⟨ r ⟩   ⟧₂ = rol I r
I ⟦ ⟨ r ⟩⁻¹ ⟧₂ = (rol I r)⁻¹

_⟦_⟧₁ : ∀ I → Concept Σ → Subset (Δ I)
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

⟦⟧₂-resp-≈ : ∀ I R {w x y z} → 
  (I ⊨ w ≈ x) → ((x , y) ∈ I ⟦ R ⟧₂) → (I ⊨ y ≈ z) → ((w , z) ∈ I ⟦ R ⟧₂) 
⟦⟧₂-resp-≈ I ⟨ r ⟩   w≈x xy∈⟦r⟧ y≈z = rol-≈ I r w≈x xy∈⟦r⟧ y≈z
⟦⟧₂-resp-≈ I ⟨ r ⟩⁻¹ w≈x yx∈⟦r⟧ y≈z = rol-≈ I r (≈-sym I y≈z) yx∈⟦r⟧ (≈-sym I w≈x)

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

_⊨t_ : Interp Σ X → TBox Σ → Set
I ⊨t ε        = True
I ⊨t (T , U)  = (I ⊨t T) × (I ⊨t U)
I ⊨t (C ⊑₁ D) = I ⟦ C ⟧₁ ⊆ I ⟦ D ⟧₁
I ⊨t (Q ⊑₂ R) = I ⟦ Q ⟧₂ ⊆ I ⟦ R ⟧₂

Axioms✓ : ∀ I T {t} → (t ∈ Axioms T) → (I ⊨t T) → (I ⊨t t)
Axioms✓ I ε        ()         I⊨T
Axioms✓ I (T , U)  (inj₁ t∈T) (I⊨T , I⊨U) = Axioms✓ I T t∈T I⊨T
Axioms✓ I (T , U)  (inj₂ t∈U) (I⊨T , I⊨U) = Axioms✓ I U t∈U I⊨U
Axioms✓ I (C ⊑₁ D) refl       I⊨T         = I⊨T
Axioms✓ I (Q ⊑₂ R) refl       I⊨T         = I⊨T
