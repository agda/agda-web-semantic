open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox )
open import Web.Semantic.DL.Interp using ( Interp )
open import Web.Semantic.DL.KB using ( KB )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.KB.Minimizable using ( μKB )
open import Web.Semantic.DL.Sequent.Model using ( minimal ; minimal-model ; minimal-minimal )
open import Web.Semantic.DL.Interp.Order using ( _≤_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.DL.TBox.Model using ( _⊨t_ )

module Web.Semantic.DL.Integrity {Σ : Signature} {X : Set} where

-- A variant of the notion of OWL integrity in:

--   Boris Motik, Ian Horrocks, and Ulrike Sattler. Bridging the gap between OWL and
--   relational databases. In Proc. Conf. World Wide Web (WWW2007), pp 807–816, 2007.

-- They propose defining that an integrity constraint S (given as a T-Box) is valid
-- for a knowlege base K whenever S is valid in every minimal Herbrand model.
-- We strengthen this requirement to say that there is a minimal model of K,
-- which validtes S.

record _⊨mm_ (K : KB Σ X) (S : TBox Σ) : Set₁ where
  field
    I : Interp Σ X
    I⊨K : I ⊨ K
    μJ⊨K : ∀ J → (J ⊨ K) → (I ≤ J)
    I⊨S : I ⊨t S

-- In the case of minimizable KBs, it suffices to check satisfaction in the proof-theoretic model.

minimal✓ : ∀ {K} → (K ∈ μKB) → ∀ S → (minimal K ⊨t S) → (K ⊨mm S)
minimal✓ {K} μK S I⊨S = record
  { I = minimal K
  ; I⊨K = minimal-model μK
  ; μJ⊨K = minimal-minimal K
  ; I⊨S = I⊨S
  }