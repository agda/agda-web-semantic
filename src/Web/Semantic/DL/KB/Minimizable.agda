open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox.Minimizable using ( μABox )
open import Web.Semantic.DL.KB using ( KB ; tbox ; abox )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox.Minimizable using ( μTBox )

module Web.Semantic.DL.KB.Minimizable {Σ : Signature} {X : Set} where

data μKB (K : KB Σ X) : Set where
  _▷_ : (tbox K ∈ μTBox) → (abox K ∈ μABox) → (K ∈ μKB)

μtbox : ∀ {K} → (K ∈ μKB) → (tbox K ∈ μTBox)
μtbox (μT ▷ μA) = μT

μabox : ∀ {K} → (K ∈ μKB) → (abox K ∈ μABox)
μabox (μT ▷ μA) = μA
