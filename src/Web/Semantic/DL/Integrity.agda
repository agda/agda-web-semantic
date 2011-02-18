open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox )
open import Web.Semantic.DL.ABox.Minimizable using ( Minimizable′ )
open import Web.Semantic.DL.Model using ( _⊨_ ; _⊨_▷_ )
open import Web.Semantic.DL.Model.Interp using ( Interp )
open import Web.Semantic.DL.Model.Minimal using ( minimal ; minimal-model ; minimal-minimal )
open import Web.Semantic.DL.Model.Order using ( _≤_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.DL.TBox.Minimizable using ( Minimizable )

module Web.Semantic.DL.Integrity {Σ : Signature} {X : Set} where

-- A variant of the notion of OWL integrity in:

--   Boris Motik, Ian Horrocks, and Ulrike Sattler. Bridging the gap between OWL and
--   relational databases. In Proc. Conf. World Wide Web (WWW2007), pp 807–816, 2007.

-- They propose defining that an integrity constraint S (given as a T-Box) is valid
-- for a knowlege base T ▷ A whenever S is valid in every minimal Herbrand model.
-- We strengthen this requirement to say that there is a minimal model of T ▷ A,
-- and that S is valid in it.

record _▷_⊨_ (T : TBox Σ) (A : ABox Σ X) (S : TBox Σ) : Set₁ where
  field
    I : Interp Σ X
    I⊨T▷A : I ⊨ T ▷ A
    μJ⊨T▷A : ∀ J → (J ⊨ T ▷ A) → (I ≤ J)
    I⊨S : I ⊨ S

-- In the case of minimizable KBs, it suffices to check satisfaction in the proof-theoretic model.

minimal✓ : ∀ {T A} → (T ∈ Minimizable) → (A ∈ Minimizable′) → ∀ S → (minimal T A ⊨ S) → (T ▷ A ⊨ S)
minimal✓ {T} {A} T↓ A↓ S I⊨S = record
  { I = minimal T A
  ; I⊨T▷A = minimal-model T↓ A↓
  ; μJ⊨T▷A = minimal-minimal T A
  ; I⊨S = I⊨S
  }