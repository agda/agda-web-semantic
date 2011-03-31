open import Data.Product using ( _×_ ; _,_ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.Util using ( Finite )

module Web.Semantic.DL.Category.Object {Σ : Signature} where

infixr 5 _,_

data Object (S T : TBox Σ) : Set₁ where
  _,_ : ∀ X → (X ∈ Finite × ABox Σ X) → Object S T

IN : ∀ {S T} → Object S T → Set
IN (X , X∈Fin , A) = X

fin : ∀ {S T} → (A : Object S T) → (IN A ∈ Finite)
fin (X , X∈Fin , A) = X∈Fin

iface : ∀ {S T} → (A : Object S T) → (ABox Σ (IN A))
iface (X , X∈Fin , A) = A
