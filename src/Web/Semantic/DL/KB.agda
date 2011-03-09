open import Web.Semantic.DL.ABox using ( ABox )
open import Web.Semantic.DL.ABox.Signature using ( Signature ; tsig )
open import Web.Semantic.DL.TBox using ( TBox )

module Web.Semantic.DL.KB where

data KB (Σ : Signature) : Set where
  _▷_ : (T : TBox (tsig Σ)) → (A : ABox Σ) → KB Σ

tbox : ∀ {Σ} → KB Σ → TBox (tsig Σ)
tbox (T ▷ A) = T

abox : ∀ {Σ} → KB Σ → ABox Σ
abox (T ▷ A) = A
