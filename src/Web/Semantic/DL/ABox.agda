open import Data.Product using ( ∃ ; _×_ ; _,_ )
open import Relation.Binary.PropositionalEquality using
  ( _≡_ ; refl ; trans ; cong₂ )
open import Relation.Unary using ( ∅ ; _∪_ )
open import Web.Semantic.DL.Signature using ( Signature ; CN ; RN )
open import Web.Semantic.Util using ( id ; _∘_ ; Subset ; ⁅_⁆ )

module Web.Semantic.DL.ABox where

infixr 5 _∼_ _∈₁_ _∈₂_
infixr 4 _,_

data ABox (Σ : Signature) (X : Set) : Set where
  ε : ABox Σ X
  _,_ : (A B : ABox Σ X) → ABox Σ X
  _∼_ : (x y : X) → ABox Σ X
  _∈₁_ : (x : X) → (c : CN Σ) → ABox Σ X
  _∈₂_ : (xy : X × X) → (r : RN Σ) → ABox Σ X

⟨ABox⟩ : ∀ {Σ X Y} → (X → Y) → ABox Σ X → ABox Σ Y
⟨ABox⟩ f ε              = ε
⟨ABox⟩ f (A , B)        = (⟨ABox⟩ f A , ⟨ABox⟩ f B)
⟨ABox⟩ f (x ∼ y)        = (f x ∼ f y)
⟨ABox⟩ f (x ∈₁ C)       = (f x ∈₁ C)
⟨ABox⟩ f ((x , y) ∈₂ R) = ((f x , f y) ∈₂ R)

⟨ABox⟩-resp-id : ∀ {Σ X} (A : ABox Σ X) → (⟨ABox⟩ id A ≡ A)
⟨ABox⟩-resp-id ε = refl
⟨ABox⟩-resp-id (A , B) = cong₂ _,_ (⟨ABox⟩-resp-id A) (⟨ABox⟩-resp-id B)
⟨ABox⟩-resp-id (x ∼ y) = refl
⟨ABox⟩-resp-id (x ∈₁ c) = refl
⟨ABox⟩-resp-id ((x , y) ∈₂ r) = refl

⟨ABox⟩-resp-∘ : ∀ {Σ X Y Z} (f : Y → Z) (g : X → Y) (A : ABox Σ X) → (⟨ABox⟩ f (⟨ABox⟩ g A) ≡ ⟨ABox⟩ (f ∘ g) A)
⟨ABox⟩-resp-∘ f g ε = refl
⟨ABox⟩-resp-∘ f g (A , B) = cong₂ _,_ (⟨ABox⟩-resp-∘ f g A) (⟨ABox⟩-resp-∘ f g B)
⟨ABox⟩-resp-∘ f g (x ∼ y) = refl
⟨ABox⟩-resp-∘ f g (x ∈₁ c) = refl
⟨ABox⟩-resp-∘ f g ((x , y) ∈₂ r) = refl

⟨ABox⟩-resp-∘² : ∀ {Σ W X Y Z} (f : Y → Z) (g : X → Y) (h : W → X) →
  ∀ (A : ABox Σ W) → (⟨ABox⟩ f (⟨ABox⟩ g (⟨ABox⟩ h A)) ≡ ⟨ABox⟩ (f ∘ g ∘ h) A)
⟨ABox⟩-resp-∘² f g h A = 
  trans (⟨ABox⟩-resp-∘ f g (⟨ABox⟩ h A)) (⟨ABox⟩-resp-∘ (f ∘ g) h A)

Assertions : ∀ {Σ X} → ABox Σ X → Subset (ABox Σ X)
Assertions ε         = ∅
Assertions (A , B)   = (Assertions A) ∪ (Assertions B)
Assertions (x ∼ y)   = ⁅ x ∼ y ⁆
Assertions (x ∈₁ c)  = ⁅ x ∈₁ c ⁆
Assertions (xy ∈₂ r) = ⁅ xy ∈₂ r ⁆
