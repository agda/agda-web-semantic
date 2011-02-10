open import Data.Product using ( ∃ ; _×_ ; _,_ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Data.Unit using ( tt ) renaming ( ⊤ to True )
open import Level using ( zero )
open import Relation.Binary using ( Setoid )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Relation.Nullary using ( ¬_ )
open import Relation.Unary using ( _∈_ ; _⊆_ ; ∅ ; U ; _∪_ ; _∩_ )
open import Web.Semantic.DL.ABox using ( ABox ; Assertions ; ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.Model.Interp using ( Interp ; Δ ; _⊨_≈_ ; ≈-refl ; ≈-sym ; ind ; con ; rol ; con-≈ ; rol-≈ )
open import Web.Semantic.DL.Signature using ( Signature ; IN ; CN ; RN )
open import Web.Semantic.DL.TBox using
  ( Concept ; Role ; TBox ; Axioms
  ; ⟨_⟩ ; ⟨_⟩⁻¹ ; ⊤ ; ⊥ ; _⊓_ ; _⊔_ ; _⇒_ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1
  ; ε ; _,_ ;_⊑₁_ ; _⊑₂_ )
open import Web.Semantic.Util using ( Subset ; _⁻¹ ; _⊃_ )

module Web.Semantic.DL.Model {Σ : Signature} where

infixr 2 _⊨_ _⊨′_ _⊨_▷_

_⟦_⟧₂ : ∀ I → Role Σ → Subset (Δ I × Δ I)
I ⟦ ⟨ r ⟩   ⟧₂ = rol I r
I ⟦ ⟨ r ⟩⁻¹ ⟧₂ = (rol I r)⁻¹

_⟦_⟧₁ : ∀ I → Concept Σ → Subset (Δ I)
I ⟦ ⟨ c ⟩    ⟧₁ = con I c
I ⟦ ⊤        ⟧₁ = U
I ⟦ ⊥        ⟧₁ = ∅
I ⟦ C ⊓ D    ⟧₁ = I ⟦ C ⟧₁ ∩ I ⟦ D ⟧₁
I ⟦ C ⊔ D    ⟧₁ = I ⟦ C ⟧₁ ∪ I ⟦ D ⟧₁
I ⟦ C ⇒ D    ⟧₁ = I ⟦ C ⟧₁ ⊃ I ⟦ D ⟧₁
I ⟦ ∀[ R ] C ⟧₁ = λ x → ∀   y → ((x , y) ∈ I ⟦ R ⟧₂) → (y ∈ I ⟦ C ⟧₁)
I ⟦ ∃⟨ R ⟩ C ⟧₁ = λ x → ∃ λ y → ((x , y) ∈ I ⟦ R ⟧₂) × (y ∈ I ⟦ C ⟧₁)
I ⟦ ≤1 R     ⟧₁ = λ x → ∀ y z → ((x , y) ∈ I ⟦ R ⟧₂) → ((x , z) ∈ I ⟦ R ⟧₂) → (I ⊨ y ≈ z)

_⟦_⟧₀ : ∀ I → IN Σ → Δ I
I ⟦ i ⟧₀ = ind I i

⟦⟧₂-resp-≈ : ∀ I R {w x y z} → 
  (I ⊨ w ≈ x) → ((x , y) ∈ I ⟦ R ⟧₂) → (I ⊨ y ≈ z) → ((w , z) ∈ I ⟦ R ⟧₂) 
⟦⟧₂-resp-≈ I ⟨ r ⟩   w≈x xy∈⟦r⟧ y≈z = rol-≈ I r w≈x xy∈⟦r⟧ y≈z
⟦⟧₂-resp-≈ I ⟨ r ⟩⁻¹ w≈x yx∈⟦r⟧ y≈z = rol-≈ I r (≈-sym I y≈z) yx∈⟦r⟧ (≈-sym I w≈x)

⟦⟧₁-resp-≈ : ∀ I C {x y} → (x ∈ I ⟦ C ⟧₁) → (I ⊨ x ≈ y) → (y ∈ I ⟦ C ⟧₁) 
⟦⟧₁-resp-≈ I ⟨ c ⟩      x∈⟦c⟧               x≈y = con-≈ I c x∈⟦c⟧ x≈y
⟦⟧₁-resp-≈ I ⊤          x∈⊤                 x≈y = tt
⟦⟧₁-resp-≈ I (C ⊓ D)    (x∈⟦C⟧ , x∈⟦D⟧)     x≈y = (⟦⟧₁-resp-≈ I C x∈⟦C⟧ x≈y , ⟦⟧₁-resp-≈ I D x∈⟦D⟧ x≈y)
⟦⟧₁-resp-≈ I (C ⊔ D)    (inj₁ x∈⟦C⟧)        x≈y = inj₁ (⟦⟧₁-resp-≈ I C x∈⟦C⟧ x≈y)
⟦⟧₁-resp-≈ I (C ⊔ D)    (inj₂ x∈⟦D⟧)        x≈y = inj₂ (⟦⟧₁-resp-≈ I D x∈⟦D⟧ x≈y)
⟦⟧₁-resp-≈ I (C ⇒ D)    x∈⟦C⟧⊃⟦D⟧            x≈y = λ y∈⟦C⟧ → ⟦⟧₁-resp-≈ I D (x∈⟦C⟧⊃⟦D⟧ (⟦⟧₁-resp-≈ I C y∈⟦C⟧ (≈-sym I x≈y))) x≈y
⟦⟧₁-resp-≈ I (∀[ R ] C) x∈□⟦R⟧⟦C⟧            x≈y = λ z yz∈⟦R⟧ → x∈□⟦R⟧⟦C⟧ z (⟦⟧₂-resp-≈ I R x≈y yz∈⟦R⟧ (≈-refl I))
⟦⟧₁-resp-≈ I (∃⟨ R ⟩ C) (z , xz∈⟦R⟧ , z∈⟦C⟧) x≈y = (z , ⟦⟧₂-resp-≈ I R (≈-sym I x≈y) xz∈⟦R⟧ (≈-refl I) , z∈⟦C⟧)
⟦⟧₁-resp-≈ I (≤1 R)     x∈∇⟦R⟧≈              x≈y = λ w z yw∈⟦R⟧ yz∈⟦R⟧ → x∈∇⟦R⟧≈ w z (⟦⟧₂-resp-≈ I R x≈y yw∈⟦R⟧ (≈-refl I)) (⟦⟧₂-resp-≈ I R x≈y yz∈⟦R⟧ (≈-refl I))
⟦⟧₁-resp-≈ I ⊥          ()                  x≈y

_⊨_ : Interp Σ → TBox Σ → Set
I ⊨ ε        = True
I ⊨ (T , U)  = (I ⊨ T) × (I ⊨ U)
I ⊨ (C ⊑₁ D) = I ⟦ C ⟧₁ ⊆ I ⟦ D ⟧₁
I ⊨ (Q ⊑₂ R) = I ⟦ Q ⟧₂ ⊆ I ⟦ R ⟧₂

Axioms✓ : ∀ I T {t} → (t ∈ Axioms T) → (I ⊨ T) → (I ⊨ t)
Axioms✓ I ε        ()         I⊨T
Axioms✓ I (T , U)  (inj₁ t∈T) (I⊨T , I⊨U) = Axioms✓ I T t∈T I⊨T
Axioms✓ I (T , U)  (inj₂ t∈U) (I⊨T , I⊨U) = Axioms✓ I U t∈U I⊨U
Axioms✓ I (C ⊑₁ D) refl       I⊨T         = I⊨T
Axioms✓ I (Q ⊑₂ R) refl       I⊨T         = I⊨T

_⊨′_ : Interp Σ → ABox Σ → Set
I ⊨′ ε            = True
I ⊨′ (A , B)      = (I ⊨′ A) × (I ⊨′ B)
I ⊨′ i ∼ j        = I ⊨ I ⟦ i ⟧₀ ≈ I ⟦ j ⟧₀
I ⊨′ i ∈₁ C       = I ⟦ i ⟧₀ ∈ I ⟦ C ⟧₁
I ⊨′ (i , j) ∈₂ R = (I ⟦ i ⟧₀ , I ⟦ j ⟧₀) ∈ I ⟦ R ⟧₂

Assertions✓ : ∀ I A {a} → (a ∈ Assertions A) → (I ⊨′ A) → (I ⊨′ a)
Assertions✓ I ε         ()         I⊨A
Assertions✓ I (A , B)   (inj₁ a∈A) (I⊨A , I⊨B) = Assertions✓ I A a∈A I⊨A
Assertions✓ I (A , B)   (inj₂ a∈B) (I⊨A , I⊨B) = Assertions✓ I B a∈B I⊨B
Assertions✓ I (i ∼ j)   refl       I⊨A         = I⊨A
Assertions✓ I (i ∈₁ C)  refl       I⊨A         = I⊨A
Assertions✓ I (ij ∈₂ R) refl       I⊨A         = I⊨A

_⊨_▷_ : Interp Σ → TBox Σ → ABox Σ → Set
I ⊨ T ▷ A = (I ⊨ T) × (I ⊨′ A)