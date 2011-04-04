open import Data.Product using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Data.Unit using ( tt )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Relation.Unary using ( _∈_ ; _⊆_ )
open import Web.Semantic.DL.ABox using
  ( ABox ; Assertions ; ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.ABox.Interp using 
  ( Interp ; _,_ ; ⌊_⌋ ; ind ; _*_ )
open import Web.Semantic.DL.ABox.Interp.Morphism using
  ( _≲_ ; _,_ ; ≲⌊_⌋ ; ≲-resp-ind ; _≋_ )
open import Web.Semantic.DL.ABox.Model using 
  ( _⟦_⟧₀ ; _⊨a_ ; Assertions✓ )
open import Web.Semantic.DL.Concept using
  ( ⟨_⟩ ; ¬⟨_⟩ ; ⊤ ; ⊥ ; _⊓_ ; _⊔_ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1 ; >1 )
open import Web.Semantic.DL.Concept.Model using ( _⟦_⟧₁ ; ⟦⟧₁-resp-≈ )
open import Web.Semantic.DL.Integrity using
  ( Unique ; Mediator ; Initial ; _>>_ ; _⊕_⊨_ ; _,_ )
open import Web.Semantic.DL.KB using ( KB ; tbox ; abox )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.Role using ( ⟨_⟩ ; ⟨_⟩⁻¹ )
open import Web.Semantic.DL.Role.Model using ( _⟦_⟧₂ ; ⟦⟧₂-resp-≈ )
open import Web.Semantic.DL.Sequent using 
  ( Γ ; γ ; _⊕_⊢_∼_ ; _⊕_⊢_∈₁_ ; _⊕_⊢_∈₂_ 
  ; ∼-assert ; ∼-import ;∼-refl ; ∼-sym ; ∼-trans ; ∼-≤1
  ; ∈₂-assert ; ∈₂-import ; ∈₂-resp-∼ ; ∈₂-subsum ; ∈₂-inv-I ; ∈₂-inv-E
  ; ∈₁-assert ; ∈₁-import ; ∈₁-resp-∼ ; ∈₁-subsum
  ; ∈₁-⊤-I ; ∈₁-⊓-I ; ∈₁-⊓-E₁ ; ∈₁-⊓-E₂ 
  ; ∈₁-⊔-I₁ ; ∈₁-⊔-I₂ ; ∈₁-∃-I ; ∈₁-∀-E )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox ; Axioms ; ε ; _,_ ;_⊑₁_ ; _⊑₂_ )
open import Web.Semantic.DL.TBox.Interp using 
  ( interp ; Δ ; _⊨_≈_ ; ≈-refl ; ≈-sym ; ≈-trans ; con-≈ ; rol-≈ ) renaming
  ( Interp to Interp′ )
open import Web.Semantic.DL.TBox.Interp.Morphism using
  ( morph ; ≲-image ; ≲-resp-≈ ; ≲-resp-con ; ≲-resp-rol )
open import Web.Semantic.DL.TBox.Minimizable using 
  ( LHS ; RHS ; μTBox
  ; ⟨_⟩ ; ⊤ ; ⊥ ; _⊓_ ; _⊔_ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1
  ; ε ; _,_ ;_⊑₁_ ; _⊑₂_ )
open import Web.Semantic.DL.TBox.Model using ( _⊨t_ ; Axioms✓ )
open import Web.Semantic.Util using
  ( Subset ; ⊆-refl ; id ; _∘_ ; _⊕_⊕_ ; _[⊕]_[⊕]_ ; inode ; bnode ; enode )

module Web.Semantic.DL.Sequent.Model {Σ : Signature} {W X Y : Set} where

infix 5 _⊞_

minimal′ : Interp Σ X → KB Σ (X ⊕ W ⊕ Y) → Interp′ Σ
minimal′ I KB = 
  interp (Γ I KB) (λ x y → (I ⊕ KB ⊢ x ∼ y)) ∼-refl ∼-sym ∼-trans
    (λ c x → I ⊕ KB ⊢ x ∈₁ ⟨ c ⟩) (λ r xy → I ⊕ KB ⊢ xy ∈₂ ⟨ r ⟩)
    (λ c → ∈₁-resp-∼) (λ r → ∈₂-resp-∼)

minimal : Interp Σ X → KB Σ (X ⊕ W ⊕ Y) → Interp Σ (X ⊕ W ⊕ Y)
minimal I KB = (minimal′ I KB , γ I KB)

complete₂ : ∀ I KB R {xy} → (xy ∈ minimal′ I KB ⟦ R ⟧₂) → (I ⊕ KB ⊢ xy ∈₂ R)
complete₂ I KB ⟨ r ⟩   {(x , y)} xy∈⟦r⟧ = xy∈⟦r⟧
complete₂ I KB ⟨ r ⟩⁻¹ {(x , y)} yx∈⟦r⟧ = ∈₂-inv-I yx∈⟦r⟧

complete₁ : ∀ I KB {C x} → (C ∈ LHS) → (x ∈ minimal′ I KB ⟦ C ⟧₁) → 
  (I ⊕ KB ⊢ x ∈₁ C)
complete₁ I KB ⟨ c ⟩ x∈⟦c⟧ = 
  x∈⟦c⟧
complete₁ I KB ⊤ _ =
  ∈₁-⊤-I
complete₁ I KB (C ⊓ D) (x∈⟦C⟧ , x∈⟦D⟧) =
  ∈₁-⊓-I (complete₁ I KB C x∈⟦C⟧) (complete₁ I KB D x∈⟦D⟧)
complete₁ I KB (C ⊔ D) (inj₁ x∈⟦C⟧) =
  ∈₁-⊔-I₁ (complete₁ I KB C x∈⟦C⟧)
complete₁ I KB (C ⊔ D) (inj₂ x∈⟦D⟧) =
  ∈₁-⊔-I₂ (complete₁ I KB D x∈⟦D⟧)
complete₁ I KB (∃⟨ R ⟩ C) (y , xy∈⟦R⟧ , y∈⟦C⟧) =
  ∈₁-∃-I (complete₂ I KB R xy∈⟦R⟧) (complete₁ I KB C y∈⟦C⟧)
complete₁ I KB ⊥ ()

sound₂ : ∀ I KB R {xy} → (I ⊕ KB ⊢ xy ∈₂ R) → (xy ∈ minimal′ I KB ⟦ R ⟧₂)
sound₂ I KB ⟨ r ⟩   {(x , y)} ⊢xy∈r  = ⊢xy∈r
sound₂ I KB ⟨ r ⟩⁻¹ {(x , y)} ⊢xy∈r⁻ = ∈₂-inv-E ⊢xy∈r⁻

sound₁ : ∀ I KB {C x} → (C ∈ RHS) → (I ⊕ KB ⊢ x ∈₁ C) → 
  (x ∈ minimal′ I KB ⟦ C ⟧₁)
sound₁ I KB ⟨ c ⟩ ⊢x∈c =
  ⊢x∈c
sound₁ I KB ⊤ ⊢x∈⊤ =
  tt
sound₁ I KB (C ⊓ D) ⊢x∈C⊓D =
  (sound₁ I KB C (∈₁-⊓-E₁ ⊢x∈C⊓D) , sound₁ I KB D (∈₁-⊓-E₂ ⊢x∈C⊓D))
sound₁ I KB (∀[ R ] C) ⊢x∈∀RC = λ y xy∈⟦R⟧ → 
  sound₁ I KB C (∈₁-∀-E ⊢x∈∀RC (complete₂ I KB R xy∈⟦R⟧))
sound₁ I KB (≤1 R) ⊢x∈≤1R = λ y z xy∈⟦R⟧ xz∈⟦R⟧ → 
  ∼-≤1 ⊢x∈≤1R (complete₂ I KB R xy∈⟦R⟧) (complete₂ I KB R xz∈⟦R⟧)

minimal-⊨ : ∀ I KB → (tbox KB ∈ μTBox) → (minimal I KB ⊨ KB)
minimal-⊨ I KB μT = 
  ( minimal-tbox μT (⊆-refl (Axioms (tbox KB)))
  , minimal-abox (abox KB) (⊆-refl (Assertions (abox KB)))) where

  minimal-tbox : ∀ {T} → (T ∈ μTBox) → (Axioms T ⊆ Axioms (tbox KB)) → 
    minimal′ I KB ⊨t T 
  minimal-tbox ε ε⊆T = 
    tt
  minimal-tbox (U , V) UV⊆T =
    ( minimal-tbox U (λ u → UV⊆T (inj₁ u))
    , minimal-tbox V (λ v → UV⊆T (inj₂ v)) )
  minimal-tbox (C ⊑₁ D) C⊑₁D∈T = λ x∈⟦C⟧ → 
    sound₁ I KB D (∈₁-subsum (complete₁ I KB C x∈⟦C⟧) (C⊑₁D∈T refl))
  minimal-tbox (Q ⊑₂ R) Q⊑₁R∈T = λ xy∈⟦Q⟧ → 
    sound₂ I KB R (∈₂-subsum (complete₂ I KB Q xy∈⟦Q⟧) (Q⊑₁R∈T refl))

  minimal-abox : ∀ A → (Assertions A ⊆ Assertions (abox KB)) → 
    minimal I KB ⊨a A
  minimal-abox ε ε⊆A = 
    tt
  minimal-abox (B , C) BC⊆A =
    ( minimal-abox B (λ b → BC⊆A (inj₁ b))
    , minimal-abox C (λ c → BC⊆A (inj₂ c)) )
  minimal-abox (x ∼ y) x∼y⊆A =
    ∼-assert (x∼y⊆A refl)
  minimal-abox (x ∈₁ c) x∈C⊆A =
    sound₁ I KB ⟨ c ⟩ (∈₁-assert (x∈C⊆A refl))
  minimal-abox ((x , y) ∈₂ r) xy∈R⊆A =
    sound₂ I KB ⟨ r ⟩ (∈₂-assert (xy∈R⊆A refl))

minimal-≳ : ∀ I KB → (I ≲ inode * minimal I KB)
minimal-≳ I KB = (morph inode ∼-import ∈₁-import ∈₂-import , λ x → ∼-refl)

minimal-≲ : ∀ I KB J → (I ≲ inode * J) → (J ⊨ KB) → (minimal I KB ≲ J)
minimal-≲ I KB J I≲J (J⊨T , J⊨A) = 
  (morph f minimal-≈ minimal-con minimal-rol , fγ≈j) where 

    f : Γ I KB → Δ ⌊ J ⌋
    f = (≲-image ≲⌊ I≲J ⌋) [⊕] (ind J ∘ bnode) [⊕] (ind J ∘ enode)

    fγ≈j : ∀ x → ⌊ J ⌋ ⊨ f (γ I KB x) ≈ ind J x
    fγ≈j (inode x) = ≲-resp-ind I≲J x
    fγ≈j (bnode v) = ≈-refl ⌊ J ⌋
    fγ≈j (enode y) = ≈-refl ⌊ J ⌋

    mutual

      minimal-≈ : ∀ {x y} → (I ⊕ KB ⊢ x ∼ y) → (⌊ J ⌋ ⊨ f x ≈ f y)
      minimal-≈ (∼-assert x∼y∈A) =
        ≈-trans ⌊ J ⌋ (fγ≈j _) 
          (≈-trans ⌊ J ⌋ (Assertions✓ J (abox KB) x∼y∈A J⊨A) 
            (≈-sym ⌊ J ⌋ (fγ≈j _)))
      minimal-≈ (∼-import x≈y) =
        ≲-resp-≈ ≲⌊ I≲J ⌋ x≈y
      minimal-≈ ∼-refl =
        ≈-refl ⌊ J ⌋
      minimal-≈ (∼-sym x∼y) =
        ≈-sym ⌊ J ⌋ (minimal-≈ x∼y)
      minimal-≈ (∼-trans x∼y y∼z) =
        ≈-trans ⌊ J ⌋ (minimal-≈ x∼y) (minimal-≈ y∼z)
      minimal-≈ (∼-≤1 x∈≤1R xy∈R xz∈R) =
        minimal-con x∈≤1R _ _ (minimal-rol xy∈R) (minimal-rol xz∈R)

      minimal-con : ∀ {x C} → (I ⊕ KB ⊢ x ∈₁ C) → (f x ∈ ⌊ J ⌋ ⟦ C ⟧₁)
      minimal-con (∈₁-assert x∈c∈A) =
        con-≈ ⌊ J ⌋ _ (Assertions✓ J (abox KB) x∈c∈A J⊨A) 
          (≈-sym ⌊ J ⌋ (fγ≈j _))
      minimal-con (∈₁-import x∈⟦c⟧) =
        ≲-resp-con ≲⌊ I≲J ⌋ x∈⟦c⟧
      minimal-con {x} {C} (∈₁-resp-∼ x∈C x∼y) =
        ⟦⟧₁-resp-≈ ⌊ J ⌋ C (minimal-con x∈C) (minimal-≈ x∼y)
      minimal-con (∈₁-subsum x∈C C⊑D∈T) =
        Axioms✓ ⌊ J ⌋ (tbox KB) C⊑D∈T J⊨T (minimal-con x∈C)
      minimal-con ∈₁-⊤-I =
        tt
      minimal-con (∈₁-⊓-I x∈C x∈D) =
        (minimal-con x∈C , minimal-con x∈D)
      minimal-con (∈₁-⊓-E₁ x∈C⊓D) =
        proj₁ (minimal-con x∈C⊓D)
      minimal-con (∈₁-⊓-E₂ x∈C⊓D) =
        proj₂ (minimal-con x∈C⊓D)
      minimal-con (∈₁-⊔-I₁ x∈C) =
        inj₁ (minimal-con x∈C)
      minimal-con (∈₁-⊔-I₂ x∈D) =
        inj₂ (minimal-con x∈D)
      minimal-con (∈₁-∀-E x∈[R]C xy∈R) =
        minimal-con x∈[R]C _ (minimal-rol xy∈R)
      minimal-con (∈₁-∃-I xy∈R y∈C) =
        (_ , minimal-rol xy∈R , minimal-con y∈C)

      minimal-rol : ∀ {x y R} → (I ⊕ KB ⊢ (x , y) ∈₂ R) → 
        ((f x , f y) ∈ ⌊ J ⌋ ⟦ R ⟧₂)
      minimal-rol (∈₂-assert xy∈r∈A) =
        rol-≈ ⌊ J ⌋ _ (fγ≈j _) (Assertions✓ J (abox KB) xy∈r∈A J⊨A)
          (≈-sym ⌊ J ⌋ (fγ≈j _))
      minimal-rol (∈₂-import xy∈⟦r⟧) =
        ≲-resp-rol ≲⌊ I≲J ⌋ xy∈⟦r⟧
      minimal-rol {x} {y} {R} (∈₂-resp-∼ w∼x xy∈R y∼z) =
        ⟦⟧₂-resp-≈ ⌊ J ⌋ R (minimal-≈ w∼x) (minimal-rol xy∈R) (minimal-≈ y∼z)
      minimal-rol (∈₂-subsum xy∈Q Q⊑R∈T) =
        Axioms✓ ⌊ J ⌋ (tbox KB) Q⊑R∈T J⊨T (minimal-rol xy∈Q)
      minimal-rol (∈₂-inv-I xy∈r) =
        minimal-rol xy∈r
      minimal-rol (∈₂-inv-E xy∈r⁻) =
        minimal-rol xy∈r⁻

minimal-≋ : ∀ I KB K I≲K K⊨KB → 
  (I≲K ≋ minimal-≳ I KB >> minimal-≲ I KB K I≲K K⊨KB)
minimal-≋ I KB K I≲K (K⊨T , K⊨A) = λ x → ≈-refl ⌊ K ⌋

minimal-uniq : ∀ I KB K I≲K → 
  Unique I (minimal I KB) K (minimal-≳ I KB) I≲K
minimal-uniq I KB K I≲K J≲₁K J≲₂K I≲K≋I≲J≲₁K I≲K≋I≲J≲₂K (inode x) =
  ≈-trans ⌊ K ⌋ (≈-sym ⌊ K ⌋ (I≲K≋I≲J≲₁K x)) (I≲K≋I≲J≲₂K x)
minimal-uniq I KB K I≲K J≲₁K J≲₂K I≲K≋I≲J≲₁K I≲K≋I≲J≲₂K (bnode v) =
  ≈-trans ⌊ K ⌋ (≲-resp-ind J≲₁K (bnode v)) 
    (≈-sym ⌊ K ⌋ (≲-resp-ind J≲₂K (bnode v)))
minimal-uniq I KB K I≲K J≲₁K J≲₂K I≲K≋I≲J≲₁K I≲K≋I≲J≲₂K (enode y) = 
  ≈-trans ⌊ K ⌋ (≲-resp-ind J≲₁K (enode y))
    (≈-sym ⌊ K ⌋ (≲-resp-ind J≲₂K (enode y)))

minimal-med : ∀ I KB → Mediator I (minimal I KB) (minimal-≳ I KB) KB
minimal-med I KB K I≲K K⊨KB = 
  ( minimal-≲ I KB K I≲K K⊨KB
  , minimal-≋ I KB K I≲K K⊨KB
  , minimal-uniq I KB K I≲K)

minimal-init : ∀ I KB → (tbox KB ∈ μTBox) → Initial I KB (minimal I KB)
minimal-init I KB μKB = 
  (minimal-≳ I KB 
  , minimal-⊨ I KB μKB 
  , minimal-med I KB)

_⊞_ : Interp Σ X → KB Σ (X ⊕ W ⊕ Y) → Interp Σ Y
I ⊞ KB = enode * minimal I KB

⊞-sound : ∀ I KB₁ KB₂ → (tbox KB₁ ∈ μTBox) → (I ⊞ KB₁ ⊨ KB₂) → (I ⊕ KB₁ ⊨ KB₂)
⊞-sound I KB₁ KB₂ μKB₁ ⊨KB₂ = (minimal I KB₁ , minimal-init I KB₁ μKB₁ , ⊨KB₂)