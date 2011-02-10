module Web.Semantic.DL.Signature where

record Signature : Set₁ where
  field IN CN RN : Set

open Signature public
