open import Data.Bool using ( Bool ; true ; false ; _∧_ )
open import Data.Empty using ()
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

is : ∀ {X : Set} → Dec X → Bool
is (yes _) = true
is (no _) = false

is✓ : ∀{X x} → □(is {X} x) → X
is✓ {X} {yes x} _ = x
is✓ {X} {no _} ()
 
is! : ∀ {X x} → X → □(is {X} x)
is! {X} {yes _} x = tt
is! {X} {no ¬x} x = ¬x x
