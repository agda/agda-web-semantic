open import Data.Product using ( _×_ ; _,_ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox ; ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.ABox.Model using ( _⊨a_ )
open import Web.Semantic.DL.ABox.Signature using ( Signature )
open import Web.Semantic.DL.Concept.Model using ( ⟦⟧₁-resp-≈ )
open import Web.Semantic.DL.Concept.Skolemization using ( CSkolems ; cskolem ; cskolem-sound )
open import Web.Semantic.DL.FOL using  ( Formula ; true ; false ; _∧_ ; _∨_ ; _⇒_ ; _∈₁_ ; _∈₂_ ; _∼_ ; ∀₁ )
open import Web.Semantic.DL.FOL.Model using ( _⊨f_ )
open import Web.Semantic.DL.Interp using ( Quotient ; ≈-sym )
open import Web.Semantic.DL.Role.Skolemization using ( rskolem ; rskolem-sound ; rskolem-complete )
open import Web.Semantic.DL.Role.Model using ( ⟦⟧₂-resp-≈ )
open import Web.Semantic.Util using ( True ; tt )

module Web.Semantic.DL.ABox.Skolemization {Σ : Signature} where

ASkolems : ABox Σ → Set
ASkolems ε = True
ASkolems (A , B) = (ASkolems A) × (ASkolems B)
ASkolems (x ∼ y) = True
ASkolems (x ∈₁ C) = CSkolems C
ASkolems (xy ∈₂ R) = True

askolem : ∀ A → (ASkolems A) → Formula Σ
askolem ε Φ = true
askolem (A , B) (Φ , Ψ) = (askolem A Φ) ∧ (askolem B Ψ)
askolem (x ∼ y) Φ = x ∼ y
askolem (x ∈₁ C) Φ = cskolem C Φ x
askolem ((x , y) ∈₂ R) Φ = rskolem R x y

askolem-sound : ∀ I A Φ → (I ∈ Quotient Σ) → (I ⊨f askolem A Φ) → (I ⊨a A)
askolem-sound I ε Φ I✓ _ = tt
askolem-sound I (A , B) (Φ , Ψ) I✓ (I⊨A , I⊨B) = (askolem-sound I A Φ I✓ I⊨A , askolem-sound I B Ψ I✓ I⊨B)
askolem-sound I (x ∼ y) Φ I✓ I⊨x∼y = I⊨x∼y
askolem-sound I (x ∈₁ C) Φ I✓ I⊨x∈C = ⟦⟧₁-resp-≈ I C (cskolem-sound I C Φ x I✓ I⊨x∈C) I✓
askolem-sound I ((x , y) ∈₂ R) Φ I✓ I⊨xy∈R = ⟦⟧₂-resp-≈ I R (≈-sym I I✓) (rskolem-sound I R x y I✓ I⊨xy∈R) I✓
