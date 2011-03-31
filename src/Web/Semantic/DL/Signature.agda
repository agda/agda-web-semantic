module Web.Semantic.DL.Signature where

data Signature : Set₁ where
  _,_ : (CN RN : Set) → Signature

CN : Signature → Set
CN (CN , RN) = CN

RN : Signature → Set
RN (CN , RN) = RN
