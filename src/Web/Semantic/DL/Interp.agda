open import Data.Product using ( _×_ ; _,_ )
open import Relation.Binary using ()
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.Signature using ( Signature ; CN ; RN )
open import Web.Semantic.Util using ( Setoid ; Subset ; _∘_ )

module Web.Semantic.DL.Interp where

record Interp (Σ : Signature) (X : Set) : Set₁ where
  field 
    setoid : Setoid
  open Relation.Binary.Setoid setoid
  field
    ind : X → Carrier
    con : CN Σ → Subset Carrier
    rol : RN Σ → Subset (Carrier × Carrier)
    con-≈ : ∀ {x y} c → (x ∈ con c) → (x ≈ y) → (y ∈ con c)
    rol-≈ : ∀ {w x y z} r → (w ≈ x) → ((x , y) ∈ rol r) → (y ≈ z) → ((w , z) ∈ rol r)
  open Relation.Binary.Setoid setoid public

open Interp public using 
  ( setoid ; ind ; con ; rol ; con-≈ ; rol-≈ ) renaming 
  ( Carrier to Δ ; _≈_ to _⊨_≈_ 
  ; refl to ≈-refl ; sym to ≈-sym ; trans to ≈-trans )

⟨Interp⟩ : ∀ {Σ X Y} → (Y → X) → (Interp Σ X → Interp Σ Y)
⟨Interp⟩ f I = record
  { setoid = setoid I
  ; ind = ind I ∘ f
  ; con = con I
  ; rol = rol I
  ; con-≈ = con-≈ I
  ; rol-≈ = rol-≈ I
  }