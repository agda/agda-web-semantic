open import Relation.Unary using ( ∅ ; _∪_ )
open import Web.Semantic.DL.TBox.Signature using ( Signature ; CN ; RN )
open import Web.Semantic.Util using ( Subset ; ⁅_⁆ )

module Web.Semantic.DL.Role where

data Role (Σ : Signature) : Set where
  ⟨_⟩ : (r : RN Σ) → Role Σ
  ⟨_⟩⁻¹ : (r : RN Σ) → Role Σ

inv : ∀ {Σ} → Role Σ → Role Σ
inv ⟨ r ⟩   = ⟨ r ⟩⁻¹
inv ⟨ r ⟩⁻¹ = ⟨ r ⟩
