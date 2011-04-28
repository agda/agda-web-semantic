module Web.Semantic.DL.Category.Properties where

open import Web.Semantic.DL.Category.Properties.Equivalence public using
  ( ≣-refl ; ≣-sym ; ≣-trans )

open import Web.Semantic.DL.Category.Properties.Composition public using
  ( compose-resp-≣ ; compose-unit₁ ; compose-unit₂ ; compose-assoc )

open import Web.Semantic.DL.Category.Properties.Tensor public using
  ( tensor-resp-≣ ; tensor-resp-id ; tensor-resp-compose 
  ; symm-iso ; assoc-iso ; assoc⁻¹-iso 
  ; unit₁-iso ; unit₁⁻¹-iso ; unit₂-iso ; unit₂⁻¹-iso
  ; assoc-unit ; assoc-assoc ; assoc-symm
  ; unit₁-natural )

