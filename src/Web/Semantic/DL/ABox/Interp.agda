open import Data.Product using ( ∃ ; _,_ )
open import Web.Semantic.DL.TBox.Interp using ( Δ ) renaming ( Interp to Interp′ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.Util using  ( _∘_ )

module Web.Semantic.DL.ABox.Interp where

infixr 4 _,_
infixr 5 _*_ 

data Interp (Σ : Signature) (X : Set) : Set₁ where
  _,_ : ∀ I → (X → Δ I) → (Interp Σ X)

⌊_⌋ : ∀ {Σ X} → Interp Σ X → Interp′ Σ
⌊ I , i ⌋ = I

ind : ∀ {Σ X} → (I : Interp Σ X) → X → Δ ⌊ I ⌋
ind (I , i) = i

_*_ : ∀ {Σ X Y} → (Y → X) → Interp Σ X → Interp Σ Y
f * I = (⌊ I ⌋ , ind I ∘ f)
