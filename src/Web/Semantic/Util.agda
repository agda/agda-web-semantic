{-# OPTIONS --universe-polymorphism #-}

open import Data.Bool using ( Bool ; true ; false ; _∧_ )
open import Data.Empty using ()
open import Data.List using ( List ; [] ; _∷_ ; _++_ ; map )
open import Data.List.Any using ( here ; there )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Product using ( ∃ ; ∄ ; _×_ ; _,_ )
open import Data.Unit using ()
open import Level using ( zero )
open import Relation.Binary using ()
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Relation.Nullary using ( Dec ; yes ; no )
open import Relation.Unary using ( _∈_ ; _⊆_ )

module Web.Semantic.Util where

infixr 9 _∘_

id : ∀ {X : Set} → X → X
id x = x

_∘_ : ∀ {X Y Z : Set} → (Y → Z) → (X → Y) → (X → Z)
(f ∘ g) = λ x → f (g x)

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

smaller-excl-middle : ExclMiddle₁ → ExclMiddle
smaller-excl-middle excl-middle₁ X = X? where

  data Large : Set₁ where
    large : X → Large

  X? : Dec X
  X? with excl-middle₁ Large
  X? | yes (large x) = yes x
  X? | no ¬x         = no (λ x → ¬x (large x))

-- Some nameclashes between the standard library and semantic web terminology:
-- ⊤ and ⊥ are used for concepts, and T is used to range over T-Boxes.

open Data.Bool public using () renaming ( T to □ )
open Data.Empty public using () renaming ( ⊥ to False ; ⊥-elim to elim )
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

False∈Fin : False ∈ Finite
False∈Fin = ([] , λ ())

⊎-resp-Fin : ∀ {X Y} → (X ∈ Finite) → (Y ∈ Finite) → ((X ⊎ Y) ∈ Finite)
⊎-resp-Fin {X} {Y} (xs , ∀x∙x∈xs) (ys , ∀y∙y∈ys) = 
  ((map inj₁ xs ++ map inj₂ ys) , lemma) where

  lemma₁ : ∀ {x : X} {xs : List X} → 
    (x ∈ˡ xs) → (inj₁ x ∈ˡ (map inj₁ xs ++ map inj₂ ys))
  lemma₁ (here refl) = here refl
  lemma₁ (there x∈xs) = there (lemma₁ x∈xs)

  lemma₂ : ∀ (xs : List X) {y : Y} {ys : List Y} → 
    (y ∈ˡ ys) → (inj₂ y ∈ˡ (map inj₁ xs ++ map inj₂ ys))
  lemma₂ [] (here refl) = here refl
  lemma₂ [] (there y∈ys) = there (lemma₂ [] y∈ys)
  lemma₂ (x ∷ xs) y∈ys = there (lemma₂ xs y∈ys)

  lemma : ∀ x → (x ∈ˡ (map inj₁ xs ++ map inj₂ ys))
  lemma (inj₁ x) = lemma₁ (∀x∙x∈xs x)
  lemma (inj₂ y) = lemma₂ xs (∀y∙y∈ys y)

-- symmetric monoidal structure of sum

_⟨⊎⟩_ : ∀ {W X Y Z : Set} → (W → X) → (Y → Z) → (W ⊎ Y) → (X ⊎ Z)
_⟨⊎⟩_ f g (inj₁ x) = inj₁ (f x)
_⟨⊎⟩_ f g (inj₂ y) = inj₂ (g y)

_≡⊎≡_ : ∀ {X Y Z : Set} {f g : (X ⊎ Y) → Z} → 
  (∀ x → (f (inj₁ x) ≡ g (inj₁ x))) → (∀ x → (f (inj₂ x) ≡ g (inj₂ x))) →
    ∀ x → (f x ≡ g x)
(f₁≡g₁ ≡⊎≡ f₂≡g₂) (inj₁ x) = f₁≡g₁ x
(f₁≡g₁ ≡⊎≡ f₂≡g₂) (inj₂ y) = f₂≡g₂ y

⊎-swap : ∀ {X Y : Set} → (X ⊎ Y) → (Y ⊎ X)
⊎-swap (inj₁ x) = inj₂ x
⊎-swap (inj₂ y) = inj₁ y

⊎-assoc : ∀ {X Y Z : Set} → ((X ⊎ Y) ⊎ Z) → (X ⊎ (Y ⊎ Z))
⊎-assoc (inj₁ (inj₁ x)) = inj₁ x
⊎-assoc (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
⊎-assoc (inj₂ z) = inj₂ (inj₂ z)

⊎-assoc⁻¹ : ∀ {X Y Z : Set} → (X ⊎ (Y ⊎ Z)) → ((X ⊎ Y) ⊎ Z)
⊎-assoc⁻¹ (inj₁ x) = inj₁ (inj₁ x)
⊎-assoc⁻¹ (inj₂ (inj₁ y)) = inj₁ (inj₂ y)
⊎-assoc⁻¹ (inj₂ (inj₂ z)) = inj₂ z

⊎-unit₁ : ∀ {X : Set} → (False ⊎ X) → X
⊎-unit₁ (inj₁ ())
⊎-unit₁ (inj₂ x) = x

⊎-unit₂ : ∀ {X : Set} → (X ⊎ False) → X
⊎-unit₂ (inj₁ x) = x
⊎-unit₂ (inj₂ ())

inj⁻¹ : ∀ {X : Set} → (X ⊎ X) → X
inj⁻¹ (inj₁ x) = x
inj⁻¹ (inj₂ x) = x

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

hmerge : ∀ {V W X Y Z A : Set} →
  ((X ⊕ V ⊕ Y) → A) → ((Y ⊕ W ⊕ Z) → A) → 
    (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z) → A
hmerge f g (inode x)         = f (inode x)
hmerge f g (bnode (inode v)) = f (bnode v)
hmerge f g (bnode (bnode y)) = g (inode y)
hmerge f g (bnode (enode w)) = g (bnode w)
hmerge f g (enode z)         = g (enode z)

→-dist-⊕ : ∀ {V X Y Z : Set} → ((X ⊕ V ⊕ Y) → Z) → 
  ((X → Z) × (V → Z) × (Y → Z))
→-dist-⊕ i = ((i ∘ inode) , (i ∘ bnode) , (i ∘ enode))

up : ∀ {V₁ V₂ X₁ X₂ Y₁ Y₂} → (X₁ ⊕ V₁ ⊕ Y₁) →
  ((X₁ ⊎ X₂) ⊕ (V₁ ⊎ V₂) ⊕ (Y₁ ⊎ Y₂))
up (inode x) = inode (inj₁ x)
up (bnode v) = bnode (inj₁ v)
up (enode y) = enode (inj₁ y)

down : ∀ {V₁ V₂ X₁ X₂ Y₁ Y₂} → (X₂ ⊕ V₂ ⊕ Y₂) →
  ((X₁ ⊎ X₂) ⊕ (V₁ ⊎ V₂) ⊕ (Y₁ ⊎ Y₂))
down (inode x) = inode (inj₂ x)
down (bnode v) = bnode (inj₂ v)
down (enode y) = enode (inj₂ y)

vmerge : ∀ {V₁ V₂ X₁ X₂ Y₁ Y₂ A : Set} →
  ((X₁ ⊕ V₁ ⊕ Y₁) → A) → ((X₂ ⊕ V₂ ⊕ Y₂) → A) →
    ((X₁ ⊎ X₂) ⊕ (V₁ ⊎ V₂) ⊕ (Y₁ ⊎ Y₂)) → A
vmerge j k (inode (inj₁ x)) = j (inode x)
vmerge j k (inode (inj₂ x)) = k (inode x)
vmerge j k (bnode (inj₁ v)) = j (bnode v)
vmerge j k (bnode (inj₂ v)) = k (bnode v)
vmerge j k (enode (inj₁ y)) = j (enode y)
vmerge j k (enode (inj₂ y)) = k (enode y)
