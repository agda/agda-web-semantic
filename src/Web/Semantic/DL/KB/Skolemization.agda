open import Data.Product using ( _×_ ; _,_ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox.Signature using ( Signature )
open import Web.Semantic.DL.ABox.Skolemization using ( ASkolems ; askolem ; askolem-sound )
open import Web.Semantic.DL.FOL using  ( Formula ;  _∧_ )
open import Web.Semantic.DL.FOL.Model using ( _⊨f_ )
open import Web.Semantic.DL.Interp using ( Quotient )
open import Web.Semantic.DL.KB using ( KB ; tbox ; abox )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.TBox.Skolemization using ( TSkolems ; tskolem ; tskolem-sound )

module Web.Semantic.DL.KB.Skolemization {Σ : Signature} where


Skolems : KB Σ → Set
Skolems K = (TSkolems (tbox K)) × (ASkolems (abox K))

skolem : ∀ K → (Skolems K) → Formula Σ
skolem K (Φ , Ψ) = tskolem (tbox K) Φ ∧ askolem (abox K) Ψ

skolem-sound : ∀ I K Φ → (I ∈ Quotient Σ) → (I ⊨f skolem K Φ) → (I ⊨ K)
skolem-sound I K (Φ , Ψ) I✓ (I⊨T , I⊨A) = (tskolem-sound I (tbox K) Φ I✓ I⊨T , askolem-sound I (abox K) Ψ I✓ I⊨A)