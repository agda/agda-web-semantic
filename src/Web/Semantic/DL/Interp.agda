open import Data.Product using ( _×_ ; _,_ )
open import Relation.Binary using ( IsEquivalence )
open import Relation.Nullary using ( ¬_ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox.Signature using ( Signature ; IN ; CN ; RN )
open import Web.Semantic.Util using ( Setoid ; Subset ; _∘_ )

module Web.Semantic.DL.Interp where

record Interp (Σ : Signature) (Δ : Set) : Set₁ where
  field
    _≈_ : Δ → Δ → Set
    isEquivalence : IsEquivalence _≈_
    ind : IN Σ → Δ
    con : CN Σ → Subset Δ
    rol : RN Σ → Subset (Δ × Δ)
    con-≈ : ∀ {x y} c → (x ∈ con c) → (x ≈ y) → (y ∈ con c)
    rol-≈ : ∀ {w x y z} r → (w ≈ x) → ((x , y) ∈ rol r) → (y ≈ z) → ((w , z) ∈ rol r)
  setoid : Setoid
  setoid = record { isEquivalence = isEquivalence }
  open Relation.Binary.IsEquivalence isEquivalence public

open Interp public using 
  ( isEquivalence ; setoid ; ind ; con ; rol ; con-≈ ; rol-≈ ) renaming 
  ( _≈_ to _⊨_≈_ ; refl to ≈-refl ; sym to ≈-sym ; trans to ≈-trans )

_⊨_≉_ : ∀ {Σ Δ} → (I : Interp Σ Δ) → Δ → Δ → Set
I ⊨ x ≉ y = ¬(I ⊨ x ≈ y)

Quotient : ∀ Σ → (Interp Σ (IN Σ)) → Set
Quotient Σ I = ∀ {x} → (I ⊨ x ≈ ind I x)
