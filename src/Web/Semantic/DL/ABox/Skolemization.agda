open import Data.Product using ( _×_ ; _,_ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox ; ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.ABox.Interp using ( ⌊_⌋ ; ind )
open import Web.Semantic.DL.ABox.Model using ( _⊨a_ )
open import Web.Semantic.DL.Concept.Model using ( ⟦⟧₁-resp-≈ )
open import Web.Semantic.DL.Concept.Skolemization using ( CSkolems ; cskolem ; cskolem-sound )
open import Web.Semantic.DL.FOL using  ( Formula ; true ; _∧_ ; _∈₁_ ; _∈₂_ ; _∼_ )
open import Web.Semantic.DL.FOL.Model using ( _⊨f_ )
open import Web.Semantic.DL.Role.Skolemization using ( rskolem ; rskolem-sound )
open import Web.Semantic.DL.Role.Model using ( ⟦⟧₂-resp-≈ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.Util using ( True ; tt )

module Web.Semantic.DL.ABox.Skolemization {Σ : Signature} {X : Set} where

askolem : ∀ {Δ} → (X → Δ) → ABox Σ X → Formula Σ Δ
askolem i ε = true
askolem i (A , B) = (askolem i A) ∧ (askolem i B)
askolem i (x ∼ y) = i x ∼ i y
askolem i (x ∈₁ c) = i x ∈₁ c
askolem i ((x , y) ∈₂ r) = (i x , i y) ∈₂ r

askolem-sound : ∀ I A → (⌊ I ⌋ ⊨f askolem (ind I) A) → (I ⊨a A)
askolem-sound I ε _ = tt
askolem-sound I (A , B) (I⊨A , I⊨B) = (askolem-sound I A I⊨A , askolem-sound I B I⊨B)
askolem-sound I (x ∼ y) I⊨x∼y = I⊨x∼y
askolem-sound I (x ∈₁ c) I⊨x∈c = I⊨x∈c
askolem-sound I ((x , y) ∈₂ r) I⊨xy∈r = I⊨xy∈r
