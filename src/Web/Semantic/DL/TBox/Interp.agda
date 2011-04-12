open import Data.Product using ( ∃ ; _×_ ; _,_ )
open import Relation.Binary using ( IsEquivalence )
open import Relation.Nullary using ( ¬_ )
open import Relation.Unary using ( _∈_ ; ∅ )
open import Web.Semantic.DL.Signature using ( Signature ; CN ; RN )
open import Web.Semantic.Util using ( Setoid ; Subset ; _∘_ ; False )

module Web.Semantic.DL.TBox.Interp where

data Interp (Σ : Signature) : Set₁ where
  interp :
    (Δ : Set) → 
    (_≈_ : Δ → Δ → Set) → 
    (refl : ∀ {x} → (x ≈ x)) → 
    (sym : ∀ {x y} → (x ≈ y) → (y ≈ x)) → 
    (trans : ∀ {x y z} → (x ≈ y) → (y ≈ z) → (x ≈ z)) → 
    (con : CN Σ → Subset Δ) → 
    (rol : RN Σ → Subset (Δ × Δ)) → 
    (con-≈ : ∀ {x y} c → (x ∈ con c) → (x ≈ y) → (y ∈ con c)) →
    (rol-≈ : ∀ {w x y z} r → (w ≈ x) → ((x , y) ∈ rol r) → (y ≈ z) → ((w , z) ∈ rol r)) →
    Interp Σ

Δ : ∀ {Σ} → Interp Σ → Set
Δ (interp Δ _≈_ refl sym trans con rol con-≈ rol-≈) = Δ

_⊨_≈_ : ∀ {Σ} → (I : Interp Σ) → (Δ I) → (Δ I) → Set
_⊨_≈_ (interp Δ _≈_ refl sym trans con rol con-≈ rol-≈) = _≈_

≈-refl : ∀ {Σ} → (I : Interp Σ) → ∀ {x} → (I ⊨ x ≈ x)
≈-refl (interp Δ _≈_ refl sym trans con rol con-≈ rol-≈) = refl

≈-sym : ∀ {Σ} → (I : Interp Σ) → ∀ {x y} → (I ⊨ x ≈ y) → (I ⊨ y ≈ x)
≈-sym (interp Δ _≈_ refl sym trans con rol con-≈ rol-≈) = sym

≈-trans : ∀ {Σ} → (I : Interp Σ) → ∀ {x y z} → (I ⊨ x ≈ y) → (I ⊨ y ≈ z) → (I ⊨ x ≈ z)
≈-trans (interp Δ _≈_ refl sym trans con rol con-≈ rol-≈) = trans

con : ∀ {Σ} → (I : Interp Σ) → CN Σ → Subset (Δ I)
con (interp Δ _≈_ refl sym trans con rol con-≈ rol-≈) = con

rol : ∀ {Σ} → (I : Interp Σ) → RN Σ → Subset (Δ I × Δ I)
rol (interp Δ _≈_ refl sym trans con rol con-≈ rol-≈) = rol

con-≈ : ∀ {Σ} → (I : Interp Σ) → ∀ {x y} c → (x ∈ con I c) → (I ⊨ x ≈ y) → (y ∈ con I c)
con-≈ (interp Δ _≈_ refl sym trans con rol con-≈ rol-≈) = con-≈

rol-≈ : ∀ {Σ} → (I : Interp Σ) → ∀ {w x y z} r → (I ⊨ w ≈ x) → ((x , y) ∈ rol I r) → (I ⊨ y ≈ z) → ((w , z) ∈ rol I r)
rol-≈ (interp Δ _≈_ refl sym trans con rol con-≈ rol-≈) = rol-≈

_⊨_≉_ : ∀ {Σ} → (I : Interp Σ) → (Δ I) → (Δ I) → Set
I ⊨ x ≉ y = ¬(I ⊨ x ≈ y)

emp : ∀ {Σ} → Interp Σ
emp = interp False (λ ()) (λ {}) (λ {}) (λ {}) (λ c → ∅) (λ r → ∅) (λ {}) (λ {})
