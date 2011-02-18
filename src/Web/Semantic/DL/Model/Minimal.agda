open import Data.Product using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Data.Unit using ( tt )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Relation.Unary using ( _∈_ ; _⊆_ )
open import Web.Semantic.DL.ABox using ( ABox ; Assertions ; ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.ABox.Minimizable using 
  ( Minimizable′ ; ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.Model.Interp using ( Interp )
open import Web.Semantic.DL.Judgement using 
  ( _▷_⊢_ ; abox ; ∼-refl ; ∼-sym ; ∼-trans ; ∼-≤1
  ; ∈₂-resp-∼ ; ∈₂-subsum ; ∈₂-inv-I ; ∈₂-inv-E
  ; ∈₁-resp-∼ ; ∈₁-subsum ; ∈₁-⊤-I ; ∈₁-⊓-I ; ∈₁-⊓-E₁ ; ∈₁-⊓-E₂ ; ∈₁-⊔-I₁ ; ∈₁-⊔-I₂ ; ∈₁-⇒-E ; ∈₁-∃-I ; ∈₁-∀-E )
open import Web.Semantic.DL.Model using 
  ( _⟦_⟧₂ ; _⟦_⟧₁ ; _⟦_⟧₀ ; ⟦⟧₂-resp-≈ ; ⟦⟧₁-resp-≈ ; _⊨_ ; _⊨′_ ; _⊨_▷_ ; Axioms✓ ; Assertions✓ )
open import Web.Semantic.DL.Model.Interp using ( _⊨_≈_ ; ≈-refl ; ≈-sym ; ≈-trans )
open import Web.Semantic.DL.Model.Order using ( _≤_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using
  ( Concept ; Role ; TBox ; Axioms
  ; ⟨_⟩ ; ⟨_⟩⁻¹ ; ⊤ ; ⊥ ; _⊓_ ; _⊔_ ; _⇒_ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1
  ; ε ; _,_ ;_⊑₁_ ; _⊑₂_ )
open import Web.Semantic.DL.TBox.Minimizable using 
  ( LHS ; RHS ; Minimizable
  ; ⟨_⟩ ; ⊤ ; ⊥ ; _⊓_ ; _⊔_ ; _⇒_ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1
  ; ε ; _,_ ;_⊑₁_ ; _⊑₂_ )
open import Web.Semantic.Util using ( Subset ; ⊆-refl )

module Web.Semantic.DL.Model.Minimal {Σ : Signature} {X : Set} where

minimal : TBox Σ → ABox Σ X → Interp Σ X
minimal T A = record 
  { S = record
    { Carrier = X
    ; _≈_ = λ x y → (T ▷ A ⊢ x ∼ y)
    ; isEquivalence = record { refl = ∼-refl ; sym = ∼-sym ; trans = ∼-trans }
    }
  ; ind = λ x → x
  ; con = λ c x → T ▷ A ⊢ x ∈₁ ⟨ c ⟩
  ; rol = λ r xy → T ▷ A ⊢ xy ∈₂ ⟨ r ⟩
  ; con-≈ = λ c → ∈₁-resp-∼
  ; rol-≈ = λ r → ∈₂-resp-∼
  }

complete₂ : ∀ T A R {xy} → (xy ∈ minimal T A ⟦ R ⟧₂) → (T ▷ A ⊢ xy ∈₂ R)
complete₂ T A ⟨ r ⟩   {(x , y)} xy∈⟦r⟧ = xy∈⟦r⟧
complete₂ T A ⟨ r ⟩⁻¹ {(x , y)} yx∈⟦r⟧ = ∈₂-inv-I yx∈⟦r⟧

complete₁ : ∀ T A {C x} → (C ∈ LHS) → (x ∈ minimal T A ⟦ C ⟧₁) → (T ▷ A ⊢ x ∈₁ C)
complete₁ T A ⟨ c ⟩      x∈⟦c⟧                = x∈⟦c⟧
complete₁ T A ⊤          _                    = ∈₁-⊤-I
complete₁ T A (C ⊓ D)    (x∈⟦C⟧ , x∈⟦D⟧)      = ∈₁-⊓-I (complete₁ T A C x∈⟦C⟧) (complete₁ T A D x∈⟦D⟧)
complete₁ T A (C ⊔ D)    (inj₁ x∈⟦C⟧)         = ∈₁-⊔-I₁ (complete₁ T A C x∈⟦C⟧)
complete₁ T A (C ⊔ D)    (inj₂ x∈⟦D⟧)         = ∈₁-⊔-I₂ (complete₁ T A D x∈⟦D⟧)
complete₁ T A (∃⟨ R ⟩ C) (y , xy∈⟦R⟧ , y∈⟦C⟧) = ∈₁-∃-I (complete₂ T A R xy∈⟦R⟧) (complete₁ T A C y∈⟦C⟧)
complete₁ T A ⊥          ()

sound₂ : ∀ T A R {xy} → (T ▷ A ⊢ xy ∈₂ R) → (xy ∈ minimal T A ⟦ R ⟧₂)
sound₂ T A ⟨ r ⟩   {(x , y)} ⊢xy∈r  = ⊢xy∈r
sound₂ T A ⟨ r ⟩⁻¹ {(x , y)} ⊢xy∈r⁻ = ∈₂-inv-E ⊢xy∈r⁻

sound₁ : ∀ T A {C x} → (C ∈ RHS) → (T ▷ A ⊢ x ∈₁ C) → (x ∈ minimal T A ⟦ C ⟧₁)
sound₁ T A ⟨ c ⟩      ⊢x∈c   = ⊢x∈c
sound₁ T A ⊤          ⊢x∈⊤   = tt
sound₁ T A (C ⊓ D)    ⊢x∈C⊓D = (sound₁ T A C (∈₁-⊓-E₁ ⊢x∈C⊓D) , sound₁ T A D (∈₁-⊓-E₂ ⊢x∈C⊓D))
sound₁ T A (C ⇒ D)    ⊢x∈C⇒D = λ x∈⟦C⟧ → sound₁ T A D (∈₁-⇒-E ⊢x∈C⇒D (complete₁ T A C x∈⟦C⟧))
sound₁ T A (∀[ R ] C) ⊢x∈∀RC = λ y xy∈⟦R⟧ → sound₁ T A C (∈₁-∀-E ⊢x∈∀RC (complete₂ T A R xy∈⟦R⟧))
sound₁ T A (≤1 R)     ⊢x∈≤1R = λ y z xy∈⟦R⟧ xz∈⟦R⟧ → ∼-≤1 ⊢x∈≤1R (complete₂ T A R xy∈⟦R⟧) (complete₂ T A R xz∈⟦R⟧)

minimal-model : ∀ {T A} → (T ∈ Minimizable) → (A ∈ Minimizable′) → (minimal T A ⊨ T ▷ A)
minimal-model {T} {A} T↓ A↓ = (minimal-tbox T↓ (⊆-refl (Axioms T)), minimal-abox A↓ (⊆-refl (Assertions A))) where

  minimal-tbox : ∀ {U} → (U ∈ Minimizable) → (Axioms U ⊆ Axioms T) → minimal T A ⊨ U 
  minimal-tbox ε        ε⊆T    = tt
  minimal-tbox (U , V)  UV⊆T   = (minimal-tbox U (λ u → UV⊆T (inj₁ u)) , minimal-tbox V (λ v → UV⊆T (inj₂ v)))
  minimal-tbox (C ⊑₁ D) C⊑₁D∈T = λ x∈⟦C⟧ → sound₁ T A D (∈₁-subsum (complete₁ T A C x∈⟦C⟧) (C⊑₁D∈T refl))
  minimal-tbox (Q ⊑₂ R) Q⊑₁R∈T = λ xy∈⟦Q⟧ → sound₂ T A R (∈₂-subsum (complete₂ T A Q xy∈⟦Q⟧) (Q⊑₁R∈T refl))

  minimal-abox : ∀ {B} → (B ∈ Minimizable′) → (Assertions B ⊆ Assertions A) → minimal T A ⊨′ B
  minimal-abox ε              ε⊆A    = tt
  minimal-abox (B , C)        BC⊆A   = (minimal-abox B (λ b → BC⊆A (inj₁ b)) , minimal-abox C (λ c → BC⊆A (inj₂ c)))
  minimal-abox (x ∼ y)        x∼y⊆A  = abox (x∼y⊆A refl)
  minimal-abox (x ∈₁ C)       x∈C⊆A  = sound₁ T A C (abox (x∈C⊆A refl))
  minimal-abox ((x , y) ∈₂ R) xy∈R⊆A = sound₂ T A R (abox (xy∈R⊆A refl))

minimal-minimal : ∀ T A I → (I ⊨ T ▷ A) → (minimal T A ≤ I)
minimal-minimal T A I (I⊨T , I⊨A) = record 
  { f = λ x → I ⟦ x ⟧₀
  ; ≤-resp-≈ = minimal-≈
  ; ≤-resp-ind = minimal-≈
  ; ≤-resp-con = minimal-con
  ; ≤-resp-rol = minimal-rol
  } where 
    mutual

      minimal-≈ : ∀ {x y} → (T ▷ A ⊢ x ∼ y) → (I ⊨ I ⟦ x ⟧₀ ≈ I ⟦ y ⟧₀)
      minimal-≈ (abox x∼y∈A)           = Assertions✓ I A x∼y∈A I⊨A
      minimal-≈ ∼-refl                 = ≈-refl I
      minimal-≈ (∼-sym x∼y)            = ≈-sym I (minimal-≈ x∼y)
      minimal-≈ (∼-trans x∼y y∼z)      = ≈-trans I (minimal-≈ x∼y) (minimal-≈ y∼z)
      minimal-≈ (∼-≤1 x∈≤1R xy∈R xz∈R) = minimal-con x∈≤1R _ _ (minimal-rol xy∈R) (minimal-rol xz∈R)

      minimal-con : ∀ {x C} → (T ▷ A ⊢ x ∈₁ C) → (I ⟦ x ⟧₀ ∈ I ⟦ C ⟧₁)
      minimal-con (abox x∈C∈A)                = Assertions✓ I A x∈C∈A I⊨A
      minimal-con (∈₁-resp-∼ {C = C} x∈C x∼y) = ⟦⟧₁-resp-≈ I C (minimal-con x∈C) (minimal-≈ x∼y)
      minimal-con (∈₁-subsum x∈C C⊑D∈T)       = Axioms✓ I T C⊑D∈T I⊨T (minimal-con x∈C)
      minimal-con ∈₁-⊤-I                      = tt
      minimal-con (∈₁-⊓-I x∈C x∈D)            = (minimal-con x∈C , minimal-con x∈D)
      minimal-con (∈₁-⊓-E₁ x∈C⊓D)             = proj₁ (minimal-con x∈C⊓D)
      minimal-con (∈₁-⊓-E₂ x∈C⊓D)             = proj₂ (minimal-con x∈C⊓D)
      minimal-con (∈₁-⊔-I₁ x∈C)               = inj₁ (minimal-con x∈C)
      minimal-con (∈₁-⊔-I₂ x∈D)               = inj₂ (minimal-con x∈D)
      minimal-con (∈₁-⇒-E x∈C⇒D x∈C)          = minimal-con x∈C⇒D (minimal-con x∈C)
      minimal-con (∈₁-∀-E x∈[R]C xy∈R)        = minimal-con x∈[R]C _ (minimal-rol xy∈R)
      minimal-con (∈₁-∃-I xy∈R y∈C)           = (_ , minimal-rol xy∈R , minimal-con y∈C)

      minimal-rol : ∀ {x y R} → (T ▷ A ⊢ (x , y) ∈₂ R) → ((I ⟦ x ⟧₀ , I ⟦ y ⟧₀) ∈ I ⟦ R ⟧₂)
      minimal-rol (abox xy∈R∈A)                    = Assertions✓ I A xy∈R∈A I⊨A
      minimal-rol (∈₂-resp-∼ {R = R} w∼x xy∈R y∼z) = ⟦⟧₂-resp-≈ I R (minimal-≈ w∼x) (minimal-rol xy∈R) (minimal-≈ y∼z)
      minimal-rol (∈₂-subsum xy∈Q Q⊑R∈T)           = Axioms✓ I T Q⊑R∈T I⊨T (minimal-rol xy∈Q)
      minimal-rol (∈₂-inv-I xy∈r)                  = minimal-rol xy∈r
      minimal-rol (∈₂-inv-E xy∈r⁻)                 = minimal-rol xy∈r⁻
