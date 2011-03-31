open import Data.Bool using ( Bool ; true ; false ; if_then_else_ )
open import Data.Product using ( _×_ ; _,_ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.Concept using ( Concept ; ⟨_⟩ ; ¬⟨_⟩ ; ⊤ ; ⊥ ; _⊓_ ; _⊔_ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1 ; >1 ; neg )
open import Web.Semantic.DL.Concept.Model using ( _⟦_⟧₁ ; ⟦⟧₁-resp-≈ )
open import Web.Semantic.DL.FOL using  ( Formula ; true ; false ; _∧_ ; _∈₁_ ; _∈₂_ ; _∈₁_⇒_ ; _∼_ ; _∼_⇒_ ; ∀₁ )
open import Web.Semantic.DL.FOL.Model using ( _⊨f_ )
open import Web.Semantic.DL.Role.Skolemization using ( rskolem ; rskolem⇒ ; rskolem-sound ; rskolem⇒-sound )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.Util using ( True ; tt )

module Web.Semantic.DL.Concept.Skolemization {Σ : Signature} where

CSkolems : Set → Concept Σ → Set
CSkolems Δ ⟨ c ⟩ = True
CSkolems Δ ¬⟨ c ⟩ = True
CSkolems Δ ⊤ = True
CSkolems Δ ⊥ = True
CSkolems Δ (C ⊓ D) = (CSkolems Δ C) × (CSkolems Δ D)
CSkolems Δ (C ⊔ D) = (Δ → Bool) × (CSkolems Δ C) × (CSkolems Δ D)
CSkolems Δ (∀[ R ] C) = CSkolems Δ C
CSkolems Δ (∃⟨ R ⟩ C) = (Δ → Δ) × (CSkolems Δ C)
CSkolems Δ (≤1 R) = True
CSkolems Δ (>1 R) = (Δ → Δ) × (Δ → Δ)

cskolem : ∀ {Δ} C → (CSkolems Δ C) → Δ → Formula Σ Δ
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

cskolem-sound : ∀ I C Φ x → (I ⊨f cskolem C Φ x) → (x ∈ I ⟦ C ⟧₁)
cskolem-sound I ⟨ c ⟩ Φ x x∈⟦c⟧ = x∈⟦c⟧
cskolem-sound I ¬⟨ c ⟩ Φ x x∉⟦c⟧ = x∉⟦c⟧
cskolem-sound I ⊤ Φ x _ = tt
cskolem-sound I ⊥ Φ x ()
cskolem-sound I (C ⊓ D) (Φ , Ψ) x (Fx , Gx) = 
  (cskolem-sound I C Φ x Fx , cskolem-sound I D Ψ x Gx)
cskolem-sound I (C ⊔ D) (φ , Φ , Ψ) x  F∨Gx with φ x
cskolem-sound I (C ⊔ D) (φ , Φ , Ψ) x  Fx | true  = inj₁ (cskolem-sound I C Φ x Fx)
cskolem-sound I (C ⊔ D) (φ , Φ , Ψ) x  Gx | false = inj₂ (cskolem-sound I D Ψ x Gx)
cskolem-sound I (∀[ R ] C) Φ x ∀RFx = 
  λ y xy∈R → cskolem-sound I C Φ y (rskolem⇒-sound I R x y (cskolem C Φ y) (∀RFx y) xy∈R)
cskolem-sound I (∃⟨ R ⟩ C) (φ , Ψ) x (xy∈R , Fy) = 
  ( φ x , rskolem-sound I R x (φ x) xy∈R , cskolem-sound I C Ψ (φ x) Fy )
cskolem-sound I (≤1 R) Φ x ≤1Rx = 
  λ y z xy∈R xz∈R → rskolem⇒-sound I R x z (y ∼ z) 
    (rskolem⇒-sound I R x y (rskolem⇒ R x z (y ∼ z)) (≤1Rx y z) xy∈R) xz∈R
cskolem-sound I (>1 R) (φ , ψ) x  (xy∈R , xz∈R , y≁z) =
  (φ x , ψ x , rskolem-sound I R x (φ x) xy∈R , rskolem-sound I R x (ψ x) xz∈R , y≁z)