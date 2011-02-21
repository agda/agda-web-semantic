open import Data.Bool using ( Bool ; true ; false ; _∧_ )
open import Data.Product using ( _×_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox ; ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox.Minimizable using ( RHS ; rhs? ; rhs )
open import Web.Semantic.Util using ( Subset ; □ ; □-proj₁ ; □-proj₂ )

module Web.Semantic.DL.ABox.Minimizable {Σ : Signature} {X : Set} where
 
data μABox : Subset (ABox Σ X) where
  ε : μABox ε
  _,_ : ∀ {A B} → (A ∈ μABox) → (B ∈ μABox) → ((A , B) ∈ μABox)
  _∼_ : ∀ i j → ((i ∼ j) ∈ μABox)
  _∈₁_ : ∀ i {C} → (C ∈ RHS) → ((i ∈₁ C) ∈ μABox)
  _∈₂_ : ∀ ij R → ((ij ∈₂ R) ∈ μABox)

μABox? : ABox Σ X → Bool
μABox? ε         = true
μABox? (A , B)   = μABox? A ∧ μABox? B
μABox? (i ∼ j)   = true
μABox? (i ∈₁ C)  = rhs? C
μABox? (ij ∈₂ R) = true

μaBox : (A : ABox Σ X) {A✓ : □(μABox? A)} → μABox A
μaBox ε               = ε
μaBox (A , B)   {AB✓} = (μaBox A {□-proj₁ AB✓} , μaBox B {□-proj₂ {μABox? A} AB✓})
μaBox (i ∼ j)         = i ∼ j
μaBox (i ∈₁ C)  {C✓}  = i ∈₁ (rhs C {C✓})
μaBox (ij ∈₂ R)       = ij ∈₂ R
