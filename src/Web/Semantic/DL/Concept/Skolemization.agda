open import Data.Bool using ( Bool ; true ; false ; if_then_else_ )
open import Data.Product using ( _×_ ; _,_ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox.Signature using ( Signature ; IN ; tsig )
open import Web.Semantic.DL.Concept using ( Concept ; ⟨_⟩ ; ¬⟨_⟩ ; ⊤ ; ⊥ ; _⊓_ ; _⊔_ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1 ; >1 ; neg )
open import Web.Semantic.DL.Concept.Model using ( _⟦_⟧₁ ; ⟦⟧₁-resp-≈ )
open import Web.Semantic.DL.FOL using  ( Formula ; true ; false ; _∧_ ; _∈₁_ ; _∈₂_ ; _∈₁_⇒_ ; _∼_ ; _∼_⇒_ ; ∀₁ )
open import Web.Semantic.DL.FOL.Model using ( _⊨f_ )
open import Web.Semantic.DL.Interp using ( Interp ; Quotient ; ind ; ≈-sym ; ≈-trans )
open import Web.Semantic.DL.Role.Skolemization using ( rskolem ; rskolem⇒ ; rskolem-sound ; rskolem⇒-sound )
open import Web.Semantic.Util using ( True ; tt )

module Web.Semantic.DL.Concept.Skolemization {Σ : Signature} where

CSkolems : Concept (tsig Σ) → Set
CSkolems ⟨ c ⟩ = True
CSkolems ¬⟨ c ⟩ = True
CSkolems ⊤ = True
CSkolems ⊥ = True
CSkolems (C ⊓ D) = (CSkolems C) × (CSkolems D)
CSkolems (C ⊔ D) = (IN Σ → Bool) × (CSkolems C) × (CSkolems D)
CSkolems (∀[ R ] C) = CSkolems C
CSkolems (∃⟨ R ⟩ C) = (IN Σ → IN Σ) × (CSkolems C)
CSkolems (≤1 R) = True
CSkolems (>1 R) = (IN Σ → IN Σ) × (IN Σ → IN Σ)

cskolem : ∀ C → (CSkolems C) → IN Σ → Formula Σ
cskolem ⟨ c ⟩ Φ x = x ∈₁ c
cskolem ¬⟨ c ⟩ Φ x = x ∈₁ c ⇒ false
cskolem ⊤ Φ x = true
cskolem ⊥ Φ x = false
cskolem (C ⊓ D) (Φ , Ψ) x = (cskolem C Φ x) ∧ (cskolem D Ψ x)
cskolem (C ⊔ D) (φ , Φ , Ψ) x = if (φ x) then (cskolem C Φ x) else (cskolem D Ψ x)
cskolem (∀[ R ] C) Φ x = ∀₁ λ y → rskolem⇒ R x y (cskolem C Φ y)
cskolem (∃⟨ R ⟩ C) (φ , Ψ) x = (rskolem R x (φ x)) ∧ (cskolem C Ψ (φ x))
cskolem (≤1 R) Φ x = ∀₁ λ y → ∀₁ λ z → rskolem⇒ R x y (rskolem⇒ R x z (y ∼ z))
cskolem (>1 R) (φ , ψ) x = (rskolem R x (φ x)) ∧ (rskolem R x (ψ x)) ∧ (φ x ∼ ψ x ⇒ false)

cskolem-sound : ∀ I C Φ x → (I ∈ Quotient Σ) → (I ⊨f cskolem C Φ x) → (x ∈ I ⟦ C ⟧₁)
cskolem-sound I ⟨ c ⟩ Φ x I✓ x∈c = ⟦⟧₁-resp-≈ I ⟨ c ⟩ x∈c (≈-sym I I✓)
cskolem-sound I ¬⟨ c ⟩ Φ x I✓ x∉c = λ x∈c → x∉c (⟦⟧₁-resp-≈ I ⟨ c ⟩ x∈c I✓)
cskolem-sound I ⊤ Φ x I✓ _ = tt
cskolem-sound I ⊥ Φ x I✓ ()
cskolem-sound I (C ⊓ D) (Φ , Ψ) x I✓ (Fx , Gx) = 
  (cskolem-sound I C Φ x I✓ Fx , cskolem-sound I D Ψ x I✓ Gx)
cskolem-sound I (C ⊔ D) (φ , Φ , Ψ) x  I✓ F∨Gx with φ x
cskolem-sound I (C ⊔ D) (φ , Φ , Ψ) x  I✓ Fx   | true  =
  inj₁ (cskolem-sound I C Φ x I✓ Fx)
cskolem-sound I (C ⊔ D) (φ , Φ , Ψ) x  I✓ Gx   | false = 
  inj₂ (cskolem-sound I D Ψ x I✓ Gx)
cskolem-sound I (∀[ R ] C) Φ x I✓ ∀RFx = 
  λ y xy∈R → cskolem-sound I C Φ y I✓ (rskolem⇒-sound I R x y (cskolem C Φ y) I✓ (∀RFx y) xy∈R)
cskolem-sound I (∃⟨ R ⟩ C) (φ , Ψ) x I✓ (xy∈R , Fy) = 
  ( φ x , rskolem-sound I R x (φ x) I✓ xy∈R , cskolem-sound I C Ψ (φ x) I✓ Fy )
cskolem-sound I (≤1 R) Φ x I✓ ≤1Rx = 
  λ y z xy∈R xz∈R → ≈-trans I I✓ (≈-trans I
    (rskolem⇒-sound I R _ _ _ I✓ 
      (rskolem⇒-sound I R _ _ _ I✓ (≤1Rx y z) xy∈R) 
      xz∈R)
    (≈-sym I I✓))
cskolem-sound I (>1 R) (φ , ψ) x  I✓ (xy∈R , xz∈R , y≁z) =
  (φ x , ψ x , rskolem-sound I R x (φ x) I✓ xy∈R , rskolem-sound I R x (ψ x) I✓ xz∈R , λ y∼z → y≁z (≈-trans I (≈-sym I I✓) (≈-trans I y∼z I✓)))