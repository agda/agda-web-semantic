open import Data.Product using ( _×_ ; _,_ )
open import Level using ( zero )
open import Relation.Binary using ( Setoid )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.Signature using ( Signature ; CN ; RN )
open import Web.Semantic.Util using ( Subset )

module Web.Semantic.DL.Model.Interp where

record Interp (Σ : Signature) (X : Set) : Set₁ where
  field 
    S : Setoid zero zero
  open Relation.Binary.Setoid S
  field
    ind : X → Carrier
    con : CN Σ → Subset Carrier
    rol : RN Σ → Subset (Carrier × Carrier)
    con-≈ : ∀ {x y} c → (x ∈ con c) → (x ≈ y) → (y ∈ con c)
    rol-≈ : ∀ {w x y z} r → (w ≈ x) → ((x , y) ∈ rol r) → (y ≈ z) → ((w , z) ∈ rol r)
  open Relation.Binary.Setoid S public

open Interp public using ( ind ; con ; rol ; con-≈ ; rol-≈ )
  renaming ( Carrier to Δ ; _≈_ to _⊨_≈_ ; refl to ≈-refl ; sym to ≈-sym ; trans to ≈-trans )
