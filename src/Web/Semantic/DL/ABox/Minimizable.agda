open import Data.Bool using ( Bool ; true ; false ; _∧_ )
open import Data.Product using ( _×_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox ; ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox.Minimizable using ( RHS ; rhs? ; rhs )
open import Web.Semantic.Util using ( Subset ; □ ; □-proj₁ ; □-proj₂ )

module Web.Semantic.DL.ABox.Minimizable {Σ : Signature} {X : Set} where

data Minimizable′ : Subset (ABox Σ X) where
  ε : Minimizable′ ε
  _,_ : ∀ {A B} → (A ∈ Minimizable′) → (B ∈ Minimizable′) → ((A , B) ∈ Minimizable′)
  _∼_ : ∀ i j → ((i ∼ j) ∈ Minimizable′)
  _∈₁_ : ∀ i {C} → (C ∈ RHS) → ((i ∈₁ C) ∈ Minimizable′)
  _∈₂_ : ∀ ij R → ((ij ∈₂ R) ∈ Minimizable′)

minimizable′? : ABox Σ X → Bool
minimizable′? ε         = true
minimizable′? (A , B)   = minimizable′? A ∧ minimizable′? B
minimizable′? (i ∼ j)   = true
minimizable′? (i ∈₁ C)  = rhs? C
minimizable′? (ij ∈₂ R) = true

minimizable′ : ∀ A {A✓ : □(minimizable′? A)} → Minimizable′ A
minimizable′ ε               = ε
minimizable′ (A , B)   {AB✓} = (minimizable′ A {□-proj₁ AB✓} , minimizable′ B {□-proj₂ {minimizable′? A} AB✓})
minimizable′ (i ∼ j)         = i ∼ j
minimizable′ (i ∈₁ C)  {C✓}  = i ∈₁ (rhs C {C✓})
minimizable′ (ij ∈₂ R)       = ij ∈₂ R
