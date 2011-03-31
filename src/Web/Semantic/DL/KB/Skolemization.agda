open import Data.Product using ( _×_ ; _,_ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox.Interp using ( ⌊_⌋ ; ind )
open import Web.Semantic.DL.ABox.Skolemization using ( askolem ; askolem-sound )
open import Web.Semantic.DL.FOL using  ( Formula ;  _∧_ )
open import Web.Semantic.DL.FOL.Model using ( _⊨f_ )
open import Web.Semantic.DL.KB using ( KB ; tbox ; abox )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox.Skolemization using ( TSkolems ; tskolem ; tskolem-sound )

module Web.Semantic.DL.KB.Skolemization {Σ : Signature} {X : Set} where

Skolems : Set → KB Σ X → Set
Skolems Δ K = TSkolems Δ (tbox K)

skolem : ∀ {Δ} → (X → Δ) → ∀ K → (Skolems Δ K) → Formula Σ Δ
skolem i K Φ = tskolem (tbox K) Φ ∧ askolem i (abox K)

skolem-sound : ∀ I K Φ → (⌊ I ⌋ ⊨f skolem (ind I) K Φ) → (I ⊨ K)
skolem-sound I K Φ (I⊨T , I⊨A) = (tskolem-sound ⌊ I ⌋ (tbox K) Φ I⊨T , askolem-sound I (abox K) I⊨A)