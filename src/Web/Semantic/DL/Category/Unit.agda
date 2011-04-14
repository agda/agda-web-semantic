open import Data.Product using ( _,_ )
open import Web.Semantic.DL.ABox using ( ε )
open import Web.Semantic.DL.Category.Object using ( Object ; _,_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.Util using ( False ; False∈Fin )

module Web.Semantic.DL.Category.Unit {Σ : Signature} where

I : ∀ {S T : TBox Σ} → Object S T
I = (False , False∈Fin , ε)
