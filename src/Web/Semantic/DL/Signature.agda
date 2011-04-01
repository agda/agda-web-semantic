module Web.Semantic.DL.Signature where

infixr 4 _,_

data Signature : Set₁ where
  _,_ : (CN RN : Set) → Signature

CN : Signature → Set
CN (CN , RN) = CN

RN : Signature → Set
RN (CN , RN) = RN
