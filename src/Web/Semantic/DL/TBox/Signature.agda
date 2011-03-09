open import Data.Product using ( _×_ ; _,_ )

module Web.Semantic.DL.TBox.Signature where

record Signature : Set₁ where
  field 
    CN RN : Set

open Signature public