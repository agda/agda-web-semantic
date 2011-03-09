open import Data.Product using ( _×_ ; _,_ )
open import Web.Semantic.DL.TBox.Signature using () renaming ( Signature to TSignature )

module Web.Semantic.DL.ABox.Signature where

record Signature : Set₁ where
  field 
    tsig : TSignature
    IN : Set
  open Web.Semantic.DL.TBox.Signature.Signature tsig public

open Signature public

asig : TSignature → Set → Signature
asig Σ IN = record { tsig = Σ ; IN = IN }