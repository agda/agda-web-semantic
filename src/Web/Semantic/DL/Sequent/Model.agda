open import Data.Product using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Data.Unit using ( tt )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Relation.Unary using ( _∈_ ; _⊆_ )
open import Web.Semantic.DL.ABox using
  ( ABox ; Assertions ; ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.ABox.Minimizable using 
  ( μABox ; ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.ABox.Model using 
  ( _⟦_⟧₀ ; _⊨a_ ; Assertions✓ )
open import Web.Semantic.DL.Interp using
  ( Interp ; _⊨_≈_ ; ≈-refl ; ≈-sym ; ≈-trans )
open import Web.Semantic.DL.Interp.Order using ( _≤_ )
open import Web.Semantic.DL.KB using ( KB ; tbox ; abox )
open import Web.Semantic.DL.KB.Minimizable using ( μKB ; μtbox ; μabox )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.Sequent using 
  ( _⊢_ ; assert ; ∼-refl ; ∼-sym ; ∼-trans ; ∼-≤1
  ; ∈₂-resp-∼ ; ∈₂-subsum ; ∈₂-inv-I ; ∈₂-inv-E
  ; ∈₁-resp-∼ ; ∈₁-subsum ; ∈₁-⊤-I ; ∈₁-⊓-I ; ∈₁-⊓-E₁ ; ∈₁-⊓-E₂ 
  ; ∈₁-⊔-I₁ ; ∈₁-⊔-I₂ ; ∈₁-∃-I ; ∈₁-∀-E )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using
  ( Concept ; Role ; TBox ; Axioms
  ; ⟨_⟩ ; ⟨_⟩⁻¹ ; ⊤ ; ⊥ ; _⊓_ ; _⊔_ ; ¬ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1
  ; ε ; _,_ ;_⊑₁_ ; _⊑₂_ )
open import Web.Semantic.DL.TBox.Minimizable using 
  ( LHS ; RHS ; μTBox
  ; ⟨_⟩ ; ⊤ ; ⊥ ; _⊓_ ; _⊔_ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1
  ; ε ; _,_ ;_⊑₁_ ; _⊑₂_ )
open import Web.Semantic.DL.TBox.Model using 
  ( _⟦_⟧₂ ; _⟦_⟧₁ ; ⟦⟧₂-resp-≈ ; ⟦⟧₁-resp-≈ ; _⊨t_ ; Axioms✓ )
open import Web.Semantic.Util using ( Subset ; ⊆-refl ; id )

module Web.Semantic.DL.Sequent.Model {Σ : Signature} {X : Set} where

minimal : (K : KB Σ X) → Interp Σ X
minimal K = record 
  { setoid = record
    { Carrier = X
    ; _≈_ = λ x y → (K ⊢ x ∼ y)
    ; isEquivalence = record { refl = ∼-refl ; sym = ∼-sym ; trans = ∼-trans }
    }
  ; ind = id
  ; con = λ c x → K ⊢ x ∈₁ ⟨ c ⟩
  ; rol = λ r xy → K ⊢ xy ∈₂ ⟨ r ⟩
  ; con-≈ = λ c → ∈₁-resp-∼
  ; rol-≈ = λ r → ∈₂-resp-∼
  }

complete₂ : ∀ K R {xy} → (xy ∈ minimal K ⟦ R ⟧₂) → (K ⊢ xy ∈₂ R)
complete₂ K ⟨ r ⟩   {(x , y)} xy∈⟦r⟧ = xy∈⟦r⟧
complete₂ K ⟨ r ⟩⁻¹ {(x , y)} yx∈⟦r⟧ = ∈₂-inv-I yx∈⟦r⟧

complete₁ : ∀ K {C x} → (C ∈ LHS) → (x ∈ minimal K ⟦ C ⟧₁) → (K ⊢ x ∈₁ C)
complete₁ K ⟨ c ⟩      x∈⟦c⟧                = x∈⟦c⟧
complete₁ K ⊤          _                    = ∈₁-⊤-I
complete₁ K (C ⊓ D)    (x∈⟦C⟧ , x∈⟦D⟧)      = ∈₁-⊓-I (complete₁ K C x∈⟦C⟧) (complete₁ K D x∈⟦D⟧)
complete₁ K (C ⊔ D)    (inj₁ x∈⟦C⟧)         = ∈₁-⊔-I₁ (complete₁ K C x∈⟦C⟧)
complete₁ K (C ⊔ D)    (inj₂ x∈⟦D⟧)         = ∈₁-⊔-I₂ (complete₁ K D x∈⟦D⟧)
complete₁ K (∃⟨ R ⟩ C) (y , xy∈⟦R⟧ , y∈⟦C⟧) = ∈₁-∃-I (complete₂ K R xy∈⟦R⟧) (complete₁ K C y∈⟦C⟧)
complete₁ K ⊥          ()

sound₂ : ∀ K R {xy} → (K ⊢ xy ∈₂ R) → (xy ∈ minimal K ⟦ R ⟧₂)
sound₂ K ⟨ r ⟩   {(x , y)} ⊢xy∈r  = ⊢xy∈r
sound₂ K ⟨ r ⟩⁻¹ {(x , y)} ⊢xy∈r⁻ = ∈₂-inv-E ⊢xy∈r⁻

sound₁ : ∀ K {C x} → (C ∈ RHS) → (K ⊢ x ∈₁ C) → (x ∈ minimal K ⟦ C ⟧₁)
sound₁ K ⟨ c ⟩      ⊢x∈c   = ⊢x∈c
sound₁ K ⊤          ⊢x∈⊤   = tt
sound₁ K (C ⊓ D)    ⊢x∈C⊓D = (sound₁ K C (∈₁-⊓-E₁ ⊢x∈C⊓D) , sound₁ K D (∈₁-⊓-E₂ ⊢x∈C⊓D))
sound₁ K (∀[ R ] C) ⊢x∈∀RC = λ y xy∈⟦R⟧ → sound₁ K C (∈₁-∀-E ⊢x∈∀RC (complete₂ K R xy∈⟦R⟧))
sound₁ K (≤1 R)     ⊢x∈≤1R = λ y z xy∈⟦R⟧ xz∈⟦R⟧ → ∼-≤1 ⊢x∈≤1R (complete₂ K R xy∈⟦R⟧) (complete₂ K R xz∈⟦R⟧)

minimal-model : ∀ {K} → (K ∈ μKB) → (minimal K ⊨ K)
minimal-model {K} μK = 
  ( minimal-tbox (μtbox μK) (⊆-refl (Axioms (tbox K)))
  , minimal-abox (μabox μK) (⊆-refl (Assertions (abox K)))) where

  minimal-tbox : ∀ {T} → (T ∈ μTBox) → (Axioms T ⊆ Axioms (tbox K)) → minimal K ⊨t T 
  minimal-tbox ε        ε⊆T    = tt
  minimal-tbox (U , V)  UV⊆T   = (minimal-tbox U (λ u → UV⊆T (inj₁ u)) , minimal-tbox V (λ v → UV⊆T (inj₂ v)))
  minimal-tbox (C ⊑₁ D) C⊑₁D∈T = λ x∈⟦C⟧ → sound₁ K D (∈₁-subsum (complete₁ K C x∈⟦C⟧) (C⊑₁D∈T refl))
  minimal-tbox (Q ⊑₂ R) Q⊑₁R∈T = λ xy∈⟦Q⟧ → sound₂ K R (∈₂-subsum (complete₂ K Q xy∈⟦Q⟧) (Q⊑₁R∈T refl))

  minimal-abox : ∀ {A} → (A ∈ μABox) → (Assertions A ⊆ Assertions (abox K)) → minimal K ⊨a A
  minimal-abox ε              ε⊆A    = tt
  minimal-abox (B , C)        BC⊆A   = (minimal-abox B (λ b → BC⊆A (inj₁ b)) , minimal-abox C (λ c → BC⊆A (inj₂ c)))
  minimal-abox (x ∼ y)        x∼y⊆A  = assert (x∼y⊆A refl)
  minimal-abox (x ∈₁ C)       x∈C⊆A  = sound₁ K C (assert (x∈C⊆A refl))
  minimal-abox ((x , y) ∈₂ R) xy∈R⊆A = sound₂ K R (assert (xy∈R⊆A refl))

minimal-minimal : ∀ K I → (I ⊨ K) → (minimal K ≤ I)
minimal-minimal K I (I⊨T , I⊨A) = record 
  { f = λ x → I ⟦ x ⟧₀
  ; ≤-resp-≈ = minimal-≈
  ; ≤-resp-ind = minimal-≈
  ; ≤-resp-con = minimal-con
  ; ≤-resp-rol = minimal-rol
  } where 
    mutual

      minimal-≈ : ∀ {x y} → (K ⊢ x ∼ y) → (I ⊨ I ⟦ x ⟧₀ ≈ I ⟦ y ⟧₀)
      minimal-≈ (assert x∼y∈A)         = Assertions✓ I (abox K) x∼y∈A I⊨A
      minimal-≈ ∼-refl                 = ≈-refl I
      minimal-≈ (∼-sym x∼y)            = ≈-sym I (minimal-≈ x∼y)
      minimal-≈ (∼-trans x∼y y∼z)      = ≈-trans I (minimal-≈ x∼y) (minimal-≈ y∼z)
      minimal-≈ (∼-≤1 x∈≤1R xy∈R xz∈R) = minimal-con x∈≤1R _ _ (minimal-rol xy∈R) (minimal-rol xz∈R)

      minimal-con : ∀ {x C} → (K ⊢ x ∈₁ C) → (I ⟦ x ⟧₀ ∈ I ⟦ C ⟧₁)
      minimal-con (assert x∈C∈A)              = Assertions✓ I (abox K) x∈C∈A I⊨A
      minimal-con (∈₁-resp-∼ {C = C} x∈C x∼y) = ⟦⟧₁-resp-≈ I C (minimal-con x∈C) (minimal-≈ x∼y)
      minimal-con (∈₁-subsum x∈C C⊑D∈T)       = Axioms✓ I (tbox K) C⊑D∈T I⊨T (minimal-con x∈C)
      minimal-con ∈₁-⊤-I                      = tt
      minimal-con (∈₁-⊓-I x∈C x∈D)            = (minimal-con x∈C , minimal-con x∈D)
      minimal-con (∈₁-⊓-E₁ x∈C⊓D)             = proj₁ (minimal-con x∈C⊓D)
      minimal-con (∈₁-⊓-E₂ x∈C⊓D)             = proj₂ (minimal-con x∈C⊓D)
      minimal-con (∈₁-⊔-I₁ x∈C)               = inj₁ (minimal-con x∈C)
      minimal-con (∈₁-⊔-I₂ x∈D)               = inj₂ (minimal-con x∈D)
      minimal-con (∈₁-∀-E x∈[R]C xy∈R)        = minimal-con x∈[R]C _ (minimal-rol xy∈R)
      minimal-con (∈₁-∃-I xy∈R y∈C)           = (_ , minimal-rol xy∈R , minimal-con y∈C)

      minimal-rol : ∀ {x y R} → (K ⊢ (x , y) ∈₂ R) → ((I ⟦ x ⟧₀ , I ⟦ y ⟧₀) ∈ I ⟦ R ⟧₂)
      minimal-rol (assert xy∈R∈A)                  = Assertions✓ I (abox K) xy∈R∈A I⊨A
      minimal-rol (∈₂-resp-∼ {R = R} w∼x xy∈R y∼z) = ⟦⟧₂-resp-≈ I R (minimal-≈ w∼x) (minimal-rol xy∈R) (minimal-≈ y∼z)
      minimal-rol (∈₂-subsum xy∈Q Q⊑R∈T)           = Axioms✓ I (tbox K) Q⊑R∈T I⊨T (minimal-rol xy∈Q)
      minimal-rol (∈₂-inv-I xy∈r)                  = minimal-rol xy∈r
      minimal-rol (∈₂-inv-E xy∈r⁻)                 = minimal-rol xy∈r⁻
