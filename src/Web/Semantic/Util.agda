open import Data.Bool using ( Bool ; true ; false ; _∧_ )
open import Data.Product using ( ∃ ; _×_ ; _,_ )
open import Data.Unit using ( tt )
open import Relation.Binary.PropositionalEquality using ( _≡_ )
open import Relation.Unary using ( _∈_ ; _⊆_ )

module Web.Semantic.Util where

infixr 5 _⊃_

Subset : Set → Set₁
Subset X = X → Set

⁅_⁆ : ∀ {X} → X → Subset X
⁅ x ⁆ y = x ≡ y

⊆-refl : ∀ {X} (P : Subset X) → (P ⊆ P)
⊆-refl P x∈P = x∈P

_⊃_ : ∀ {X : Set} → Subset X → Subset X → Subset X
(P ⊃ Q) x = (x ∈ P) → (x ∈ Q)

_⁻¹ :  ∀ {X Y : Set} → Subset (X × Y) → Subset (Y × X)
(R ⁻¹) (y , x) = R (x , y)

open Data.Bool public using () renaming ( T to □ )

□-proj₁ : ∀ {b c} → □(b ∧ c) → □ b
□-proj₁ {true}  □c = tt
□-proj₁ {false} ()

□-proj₂ : ∀ {b c} → □(b ∧ c) → □ c
□-proj₂ {true}  □c = □c
□-proj₂ {false} ()
