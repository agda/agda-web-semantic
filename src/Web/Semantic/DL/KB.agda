open import Web.Semantic.DL.ABox using ( ABox )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )

module Web.Semantic.DL.KB where

data _⊕_ (W X : Set) : Set where
  bnode : (w : W) → (W ⊕ X)
  named : (x : X) → (W ⊕ X)

_[⊕]_ : ∀ {W X Z : Set} → (W → Z) → (X → Z) → (W ⊕ X) → Z
(f [⊕] g) (bnode w) = f w
(f [⊕] g) (named x) = g x

data KB (Σ : Signature) (X : Set) : Set₁ where
  _▷_ : ∀ {W} → (T : TBox Σ) → (A : ABox Σ (W ⊕ X)) → KB Σ X

BNode : ∀ {Σ X} → KB Σ X → Set
BNode (_▷_ {W} T A) = W

Named : ∀ {Σ X} → KB Σ X → Set
Named {Σ} {X} K = X

Ind : ∀ {Σ X} → KB Σ X → Set
Ind K = BNode K ⊕ Named K

tbox : ∀ {Σ X} → KB Σ X → TBox Σ
tbox (T ▷ A) = T

abox : ∀ {Σ X} (K : KB Σ X) → ABox Σ (Ind K)
abox (T ▷ A) = A
