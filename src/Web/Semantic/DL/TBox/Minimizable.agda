open import Data.Bool using ( Bool ; true ; false ; _∧_ )
open import Data.Product using ( _×_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.Concept using ( Concept ; ⟨_⟩ ; ¬⟨_⟩ ; ⊤ ; ⊥ ; _⊓_ ; _⊔_ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1 ; >1 )
open import Web.Semantic.DL.TBox.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox ; ε ; _,_ ;_⊑₁_ ; _⊑₂_ )
open import Web.Semantic.Util using ( Subset ; □ ; □-proj₁ ; □-proj₂ )

module Web.Semantic.DL.TBox.Minimizable {Σ : Signature} where

data LHS : Subset (Concept Σ) where
  ⟨_⟩ : ∀ c → ⟨ c ⟩ ∈ LHS
  ⊤ : ⊤ ∈ LHS
  ⊥ : ⊥ ∈ LHS 
  _⊓_ : ∀ {C D} → (C ∈ LHS) → (D ∈ LHS) → ((C ⊓ D) ∈ LHS)
  _⊔_ : ∀ {C D} → (C ∈ LHS) → (D ∈ LHS) → ((C ⊔ D) ∈ LHS)
  ∃⟨_⟩_ : ∀ R {C} → (C ∈ LHS) → ((∃⟨ R ⟩ C) ∈ LHS)

data RHS : Subset (Concept Σ) where
  ⟨_⟩ : ∀ c → ⟨ c ⟩ ∈ RHS
  ⊤ : ⊤ ∈ RHS
  _⊓_ : ∀ {C D} → (C ∈ RHS) → (D ∈ RHS) → ((C ⊓ D) ∈ RHS)
  ∀[_]_ : ∀ R {C} → (C ∈ RHS) → ((∀[ R ] C) ∈ RHS)
  ≤1 : ∀ R → ((≤1 R) ∈ RHS)

data μTBox : Subset (TBox Σ) where
  ε : μTBox ε
  _,_ : ∀ {T U} → (T ∈ μTBox) → (U ∈ μTBox) → ((T , U) ∈ μTBox)
  _⊑₁_ : ∀ {C D} → (C ∈ LHS) → (D ∈ RHS) → ((C ⊑₁ D) ∈ μTBox)
  _⊑₂_ : ∀ Q R → ((Q ⊑₂ R) ∈ μTBox)

lhs? : Concept Σ → Bool
lhs? ⟨ c ⟩      = true
lhs? ¬⟨ c ⟩     = false
lhs? ⊤          = true
lhs? ⊥          = true
lhs? (C ⊓ D)    = lhs? C ∧ lhs? D
lhs? (C ⊔ D)    = lhs? C ∧ lhs? D
lhs? (∀[ R ] C) = false
lhs? (∃⟨ R ⟩ C) = lhs? C
lhs? (≤1 R)     = false
lhs? (>1 R)     = false

lhs : ∀ C {C✓ : □(lhs? C)} → LHS C
lhs ⟨ c ⟩             = ⟨ c ⟩
lhs ⊤                 = ⊤
lhs ⊥                 = ⊥
lhs (C ⊓ D)    {C⊓D✓} = lhs C {□-proj₁ C⊓D✓} ⊓ lhs D {□-proj₂ {lhs? C} C⊓D✓}
lhs (C ⊔ D)    {C⊔D✓} = lhs C {□-proj₁ C⊔D✓} ⊔ lhs D {□-proj₂ {lhs? C} C⊔D✓}
lhs (∃⟨ R ⟩ C) {C✓}   = ∃⟨ R ⟩ (lhs C {C✓})
lhs ¬⟨ c ⟩     {}
lhs (∀[ R ] C) {}
lhs (≤1 R)     {}
lhs (>1 R)     {}

rhs? : Concept Σ → Bool
rhs? ⟨ c ⟩      = true
rhs? ¬⟨ c ⟩     = false
rhs? ⊤          = true
rhs? ⊥          = false
rhs? (C ⊓ D)    = rhs? C ∧ rhs? D
rhs? (C ⊔ D)    = false
rhs? (∀[ R ] C) = rhs? C
rhs? (∃⟨ R ⟩ C) = false
rhs? (≤1 R)     = true
rhs? (>1 R)     = false

rhs : ∀ C {C✓ : □(rhs? C)} → RHS C
rhs ⟨ c ⟩             = ⟨ c ⟩
rhs ⊤                 = ⊤
rhs (C ⊓ D)    {C⊓D✓} = rhs C {□-proj₁ C⊓D✓} ⊓ rhs D {□-proj₂ {rhs? C} C⊓D✓}
rhs (∀[ R ] C) {C✓}   = ∀[ R ] (rhs C {C✓})
rhs (≤1 R)            = ≤1 R
rhs ⊥          {}
rhs ¬⟨ c ⟩     {}
rhs (C ⊔ D)    {}
rhs (∃⟨ R ⟩ C) {}
rhs (>1 R)     {}

μTBox? : TBox Σ → Bool
μTBox? ε        = true
μTBox? (T , U)  = μTBox? T ∧ μTBox? U
μTBox? (C ⊑₁ D) = lhs? C ∧ rhs? D
μTBox? (Q ⊑₂ R) = true

μtBox : ∀ T {T✓ : □(μTBox? T)} → μTBox T
μtBox ε               = ε
μtBox (T , U)  {TU✓}  = (μtBox T {□-proj₁ TU✓} , μtBox U {□-proj₂ {μTBox? T} TU✓})
μtBox (C ⊑₁ D) {C⊑D✓} = lhs C {□-proj₁ C⊑D✓} ⊑₁ rhs D {□-proj₂ {lhs? C} C⊑D✓}
μtBox (Q ⊑₂ R)        = Q ⊑₂ R
