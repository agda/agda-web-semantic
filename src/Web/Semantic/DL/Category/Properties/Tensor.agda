module Web.Semantic.DL.Category.Properties.Tensor where

open import Web.Semantic.DL.Category.Properties.Tensor.RespectsEquiv public using
  ( tensor-resp-≣ )

open import Web.Semantic.DL.Category.Properties.Tensor.Functor public using
  ( tensor-resp-id ; tensor-resp-compose )

open import Web.Semantic.DL.Category.Properties.Tensor.Isomorphisms public using
  ( symm-iso ; assoc-iso ; assoc⁻¹-iso 
  ; unit₁-iso ; unit₁⁻¹-iso ; unit₂-iso ; unit₂⁻¹-iso )

open import Web.Semantic.DL.Category.Properties.Tensor.Coherence public using
  ( assoc-unit ; assoc-assoc ; assoc-symm )

open import Web.Semantic.DL.Category.Properties.Tensor.UnitNatural public using
  ( unit₁-natural )
