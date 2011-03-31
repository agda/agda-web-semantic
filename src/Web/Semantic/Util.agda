{-# OPTIONS --universe-polymorphism #-}

open import Data.Bool using ( Bool ; true ; false ; _∧_ )
open import Data.Empty using ()
open import Data.List.Any using ()
open import Data.Sum using ( _⊎_ ; inj₁ )
open import Data.Product using ( ∃ ; ∄ ; _×_ ; _,_ )
open import Data.Unit using ()
open import Level using ( zero )
open import Relation.Binary using ()
open import Relation.Binary.PropositionalEquality using ( _≡_ )
open import Relation.Nullary using ( Dec ; yes ; no )
open import Relation.Unary using ( _∈_ ; _⊆_ )

module Web.Semantic.Util where

infixr 9 _∘_

id : ∀ {X : Set} → X → X
id x = x

_∘_ : ∀ {X Y Z : Set} → (Y → Z) → (X → Y) → (X → Z)
(f ∘ g) x = f (g x)

Setoid : Set₁
Setoid = Relation.Binary.Setoid zero zero

Subset : Set → Set₁
Subset X = X → Set

⁅_⁆ : ∀ {X} → X → Subset X
⁅ x ⁆ y = x ≡ y

⊆-refl : ∀ {X} (P : Subset X) → (P ⊆ P)
⊆-refl P x∈P = x∈P

_⁻¹ :  ∀ {X Y : Set} → Subset (X × Y) → Subset (Y × X)
(R ⁻¹) (y , x) = R (x , y)

-- Some proofs are classical, and depend on excluded middle.

ExclMiddle : Set₁
ExclMiddle = ∀ (X : Set) → Dec X

ExclMiddle₁ : Set₂
ExclMiddle₁ = ∀ (X : Set₁) → Dec X

-- Some nameclashes between the standard library and semantic web terminology:
-- ⊤ and ⊥ are used for concepts, and T is used to range over T-Boxes.

open Data.Bool public using () renaming ( T to □ )
open Data.Empty public using () renaming ( ⊥ to False )
open Data.Unit public using ( tt ) renaming ( ⊤ to True )

□-proj₁ : ∀ {b c} → □(b ∧ c) → □ b
□-proj₁ {true}  □c = tt
□-proj₁ {false} ()

□-proj₂ : ∀ {b c} → □(b ∧ c) → □ c
□-proj₂ {true}  □c = □c
□-proj₂ {false} ()

-- Convert back and forth from Dec and Bool.

is : ∀ {ℓ} {X : Set ℓ} → Dec X → Bool
is (yes _) = true
is (no _) = false

is✓ : ∀ {ℓ} {X : Set ℓ} {x : Dec X} → □(is x) → X
is✓ {ℓ} {X} {yes x} _ = x
is✓ {ℓ} {X} {no _} ()
 
is! : ∀ {ℓ} {X : Set ℓ} {x : Dec X} → X → □(is x)
is! {ℓ} {X} {yes _} x = tt
is! {ℓ} {X} {no ¬x} x = ¬x x

-- Finite sets are ones backed by a list

open Data.List.Any.Membership-≡ public using () renaming ( _∈_ to _∈ˡ_ )

Finite : Set → Set
Finite X = ∃ λ xs → ∀ (x : X) → (x ∈ˡ xs)

-- A set divided, like Gaul, into three parts

infix 6 _⊕_⊕_

data _⊕_⊕_ (X V Y : Set) : Set where
  inode : (x : X) → (X ⊕ V ⊕ Y) -- Imported node
  bnode : (v : V) → (X ⊕ V ⊕ Y) -- Blank node
  enode : (y : Y) → (X ⊕ V ⊕ Y) -- Exported node

_⟨⊕⟩_⟨⊕⟩_ : ∀ {U V W X Y Z} → (W → X) → (U → V) → (Y → Z) →
  (W ⊕ U ⊕ Y) → (X ⊕ V ⊕ Z)
(f ⟨⊕⟩ g ⟨⊕⟩ h) (inode w) = inode (f w)
(f ⟨⊕⟩ g ⟨⊕⟩ h) (bnode u) = bnode (g u)
(f ⟨⊕⟩ g ⟨⊕⟩ h) (enode y) = enode (h y)

_[⊕]_[⊕]_ : ∀ {X V Y Z : Set} → (X → Z) → (V → Z) → (Y → Z) →
   (X ⊕ V ⊕ Y) → Z
(f [⊕] g [⊕] h) (inode x) = f x
(f [⊕] g [⊕] h) (bnode v) = g v
(f [⊕] g [⊕] h) (enode y) = h y

left : ∀ {V W X Y Z} → (X ⊕ V ⊕ Y) → (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z)
left (inode x) = inode x
left (bnode v) = bnode (inode v)
left (enode y) = bnode (bnode y)

right : ∀ {V W X Y Z} → (Y ⊕ W ⊕ Z) → (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z)
right (inode y) = bnode (bnode y)
right (bnode w) = bnode (enode w)
right (enode z) = enode z

merge : ∀ {V W X Y Z A : Set} →
  ((X ⊕ V ⊕ Y) → A) → ((Y ⊕ W ⊕ Z) → A) → 
    (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z) → A
merge f g (inode x)         = f (inode x)
merge f g (bnode (inode v)) = f (bnode v)
merge f g (bnode (bnode y)) = g (inode y)
merge f g (bnode (enode w)) = g (bnode w)
merge f g (enode z)         = g (enode z)
