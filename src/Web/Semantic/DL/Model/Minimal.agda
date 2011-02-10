open import Data.Product using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Data.Unit using ( tt )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Relation.Unary using ( _∈_ ; _⊆_ )
open import Web.Semantic.DL.ABox using ( ABox ; Assertions ; ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.Model.Interp using ( Interp )
open import Web.Semantic.DL.Judgement using 
  ( _▷_⊢_ ; abox ; ∼-refl ; ∼-sym ; ∼-trans ; ∼-≤1
  ; ∈₂-resp-∼ ; ∈₂-subsum ; ∈₂-inv-I ; ∈₂-inv-E
  ; ∈₁-resp-∼ ; ∈₁-subsum ; ∈₁-⊤-I ; ∈₁-⊓-I ; ∈₁-⊓-E₁ ; ∈₁-⊓-E₂ ; ∈₁-⊔-I₁ ; ∈₁-⊔-I₂ ; ∈₁-⇒-E ; ∈₁-∃-I ; ∈₁-∀-E )
open import Web.Semantic.DL.Minimizable using 
  ( LHS ; RHS ; Minimizable′ ; Minimizable
  ; ⟨_⟩ ; ⊤ ; ⊥ ; _⊓_ ; _⊔_ ; _⇒_ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1
  ; ε ; _,_ ;_⊑₁_ ; _⊑₂_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.Model using 
  ( _⟦_⟧₂ ; _⟦_⟧₁ ; _⟦_⟧₀ ; ⟦⟧₂-resp-≈ ; ⟦⟧₁-resp-≈ ; _⊨_ ; _⊨′_ ; _⊨_▷_ ; Axioms✓ ; Assertions✓ )
open import Web.Semantic.DL.Model.Interp using ( _⊨_≈_ ; ≈-refl ; ≈-sym ; ≈-trans )
open import Web.Semantic.DL.Model.Order using ( _≤_ )
open import Web.Semantic.DL.Signature using ( Signature ; IN )
open import Web.Semantic.DL.TBox using
  ( Concept ; Role ; TBox ; Axioms
  ; ⟨_⟩ ; ⟨_⟩⁻¹ ; ⊤ ; ⊥ ; _⊓_ ; _⊔_ ; _⇒_ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1
  ; ε ; _,_ ;_⊑₁_ ; _⊑₂_ )
open import Web.Semantic.Util using ( Subset ; ⊆-refl )

module Web.Semantic.DL.Model.Minimal {Σ : Signature} where

minimal : TBox Σ → ABox Σ → Interp Σ
minimal T A = record 
  { S = record
    { Carrier = IN Σ
    ; _≈_ = λ i j → (T ▷ A ⊢ i ∼ j)
    ; isEquivalence = record { refl = ∼-refl ; sym = ∼-sym ; trans = ∼-trans }
    }
  ; ind = λ i → i
  ; con = λ c i → T ▷ A ⊢ i ∈₁ ⟨ c ⟩
  ; rol = λ r ij → T ▷ A ⊢ ij ∈₂ ⟨ r ⟩
  ; con-≈ = λ c → ∈₁-resp-∼
  ; rol-≈ = λ r → ∈₂-resp-∼
  }

complete₂ : ∀ T A R {ij} → (ij ∈ minimal T A ⟦ R ⟧₂) → (T ▷ A ⊢ ij ∈₂ R)
complete₂ T A ⟨ r ⟩   {(i , j)} ij∈⟦r⟧ = ij∈⟦r⟧
complete₂ T A ⟨ r ⟩⁻¹ {(i , j)} ji∈⟦r⟧ = ∈₂-inv-I ji∈⟦r⟧

complete₁ : ∀ T A {C i} → (C ∈ LHS) → (i ∈ minimal T A ⟦ C ⟧₁) → (T ▷ A ⊢ i ∈₁ C)
complete₁ T A ⟨ c ⟩      i∈⟦c⟧                = i∈⟦c⟧
complete₁ T A ⊤          _                    = ∈₁-⊤-I
complete₁ T A (C ⊓ D)    (i∈⟦C⟧ , i∈⟦D⟧)      = ∈₁-⊓-I (complete₁ T A C i∈⟦C⟧) (complete₁ T A D i∈⟦D⟧)
complete₁ T A (C ⊔ D)    (inj₁ i∈⟦C⟧)         = ∈₁-⊔-I₁ (complete₁ T A C i∈⟦C⟧)
complete₁ T A (C ⊔ D)    (inj₂ i∈⟦D⟧)         = ∈₁-⊔-I₂ (complete₁ T A D i∈⟦D⟧)
complete₁ T A (∃⟨ R ⟩ C) (j , ij∈⟦R⟧ , j∈⟦C⟧) = ∈₁-∃-I (complete₂ T A R ij∈⟦R⟧) (complete₁ T A C j∈⟦C⟧)
complete₁ T A ⊥          ()

sound₂ : ∀ T A R {ij} → (T ▷ A ⊢ ij ∈₂ R) → (ij ∈ minimal T A ⟦ R ⟧₂)
sound₂ T A ⟨ r ⟩   {(i , j)} ⊢ij∈r  = ⊢ij∈r
sound₂ T A ⟨ r ⟩⁻¹ {(i , j)} ⊢ij∈r⁻ = ∈₂-inv-E ⊢ij∈r⁻

sound₁ : ∀ T A {C i} → (C ∈ RHS) → (T ▷ A ⊢ i ∈₁ C) → (i ∈ minimal T A ⟦ C ⟧₁)
sound₁ T A ⟨ c ⟩      ⊢i∈c   = ⊢i∈c
sound₁ T A ⊤          ⊢i∈⊤   = tt
sound₁ T A (C ⊓ D)    ⊢i∈C⊓D = (sound₁ T A C (∈₁-⊓-E₁ ⊢i∈C⊓D) , sound₁ T A D (∈₁-⊓-E₂ ⊢i∈C⊓D))
sound₁ T A (C ⇒ D)    ⊢i∈C⇒D = λ i∈⟦C⟧ → sound₁ T A D (∈₁-⇒-E ⊢i∈C⇒D (complete₁ T A C i∈⟦C⟧))
sound₁ T A (∀[ R ] C) ⊢i∈∀RC = λ j ij∈⟦R⟧ → sound₁ T A C (∈₁-∀-E ⊢i∈∀RC (complete₂ T A R ij∈⟦R⟧))
sound₁ T A (≤1 R)     ⊢i∈≤1R = λ j k ij∈⟦R⟧ ik∈⟦R⟧ → ∼-≤1 ⊢i∈≤1R (complete₂ T A R ij∈⟦R⟧) (complete₂ T A R ik∈⟦R⟧)

minimal-model : ∀ {T A} → (T ∈ Minimizable) → (A ∈ Minimizable′) → (minimal T A ⊨ T ▷ A)
minimal-model {T} {A} T↓ A↓ = (minimal-tbox T↓ (⊆-refl (Axioms T)), minimal-abox A↓ (⊆-refl (Assertions A))) where

  minimal-tbox : ∀ {U} → (U ∈ Minimizable) → (Axioms U ⊆ Axioms T) → minimal T A ⊨ U 
  minimal-tbox ε        ε⊆T    = tt
  minimal-tbox (U , V)  UV⊆T   = (minimal-tbox U (λ u → UV⊆T (inj₁ u)) , minimal-tbox V (λ v → UV⊆T (inj₂ v)))
  minimal-tbox (C ⊑₁ D) C⊑₁D∈T = λ i∈⟦C⟧ → sound₁ T A D (∈₁-subsum (complete₁ T A C i∈⟦C⟧) (C⊑₁D∈T refl))
  minimal-tbox (Q ⊑₂ R) Q⊑₁R∈T = λ ij∈⟦Q⟧ → sound₂ T A R (∈₂-subsum (complete₂ T A Q ij∈⟦Q⟧) (Q⊑₁R∈T refl))

  minimal-abox : ∀ {B} → (B ∈ Minimizable′) → (Assertions B ⊆ Assertions A) → minimal T A ⊨′ B
  minimal-abox ε              ε⊆A    = tt
  minimal-abox (B , C)        BC⊆A   = (minimal-abox B (λ b → BC⊆A (inj₁ b)) , minimal-abox C (λ c → BC⊆A (inj₂ c)))
  minimal-abox (i ∼ j)        i∼j⊆A  = abox (i∼j⊆A refl)
  minimal-abox (i ∈₁ C)       i∈C⊆A  = sound₁ T A C (abox (i∈C⊆A refl))
  minimal-abox ((i , j) ∈₂ R) ij∈R⊆A = sound₂ T A R (abox (ij∈R⊆A refl))

minimal-minimal : ∀ T A I → (I ⊨ T ▷ A) → (minimal T A ≤ I)
minimal-minimal T A I (I⊨T , I⊨A) = record 
  { f = λ i → I ⟦ i ⟧₀
  ; ≤-resp-≈ = minimal-≈
  ; ≤-resp-ind = minimal-≈
  ; ≤-resp-con = minimal-con
  ; ≤-resp-rol = minimal-rol
  } where 
    mutual

      minimal-≈ : ∀ {i j} → (T ▷ A ⊢ i ∼ j) → (I ⊨ I ⟦ i ⟧₀ ≈ I ⟦ j ⟧₀)
      minimal-≈ (abox i∼j∈A)           = Assertions✓ I A i∼j∈A I⊨A
      minimal-≈ ∼-refl                 = ≈-refl I
      minimal-≈ (∼-sym i∼j)            = ≈-sym I (minimal-≈ i∼j)
      minimal-≈ (∼-trans i∼j j∼k)      = ≈-trans I (minimal-≈ i∼j) (minimal-≈ j∼k)
      minimal-≈ (∼-≤1 i∈≤1R ij∈R ik∈R) = minimal-con i∈≤1R _ _ (minimal-rol ij∈R) (minimal-rol ik∈R)

      minimal-con : ∀ {i C} → (T ▷ A ⊢ i ∈₁ C) → (I ⟦ i ⟧₀ ∈ I ⟦ C ⟧₁)
      minimal-con (abox i∈C∈A)                = Assertions✓ I A i∈C∈A I⊨A
      minimal-con (∈₁-resp-∼ {C = C} i∈C i∼j) = ⟦⟧₁-resp-≈ I C (minimal-con i∈C) (minimal-≈ i∼j)
      minimal-con (∈₁-subsum i∈C C⊑D∈T)       = Axioms✓ I T C⊑D∈T I⊨T (minimal-con i∈C)
      minimal-con ∈₁-⊤-I                      = tt
      minimal-con (∈₁-⊓-I i∈C i∈D)            = (minimal-con i∈C , minimal-con i∈D)
      minimal-con (∈₁-⊓-E₁ i∈C⊓D)             = proj₁ (minimal-con i∈C⊓D)
      minimal-con (∈₁-⊓-E₂ i∈C⊓D)             = proj₂ (minimal-con i∈C⊓D)
      minimal-con (∈₁-⊔-I₁ i∈C)               = inj₁ (minimal-con i∈C)
      minimal-con (∈₁-⊔-I₂ i∈D)               = inj₂ (minimal-con i∈D)
      minimal-con (∈₁-⇒-E i∈C⇒D i∈C)          = minimal-con i∈C⇒D (minimal-con i∈C)
      minimal-con (∈₁-∀-E i∈[R]C ij∈R)        = minimal-con i∈[R]C _ (minimal-rol ij∈R)
      minimal-con (∈₁-∃-I ij∈R j∈C)           = (_ , minimal-rol ij∈R , minimal-con j∈C)

      minimal-rol : ∀ {i j R} → (T ▷ A ⊢ (i , j) ∈₂ R) → ((I ⟦ i ⟧₀ , I ⟦ j ⟧₀) ∈ I ⟦ R ⟧₂)
      minimal-rol (abox ij∈R∈A)                    = Assertions✓ I A ij∈R∈A I⊨A
      minimal-rol (∈₂-resp-∼ {R = R} i∼j jk∈R k∼l) = ⟦⟧₂-resp-≈ I R (minimal-≈ i∼j) (minimal-rol jk∈R) (minimal-≈ k∼l)
      minimal-rol (∈₂-subsum ij∈Q Q⊑R∈T)           = Axioms✓ I T Q⊑R∈T I⊨T (minimal-rol ij∈Q)
      minimal-rol (∈₂-inv-I ij∈r)                  = minimal-rol ij∈r
      minimal-rol (∈₂-inv-E ij∈r⁻)                 = minimal-rol ij∈r⁻
