open import Data.Product using ( ∃ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.TBox.Interp using ( Δ ; _⊨_≈_ ) renaming 
  ( Interp to Interp′ ; emp to emp′ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.Util using ( False ; id )

module Web.Semantic.DL.ABox.Interp where

infixr 4 _,_
infixr 5 _*_ 

data Interp (Σ : Signature) (X : Set) : Set₁ where
  _,_ : ∀ I → (X → Δ I) → (Interp Σ X)

⌊_⌋ : ∀ {Σ X} → Interp Σ X → Interp′ Σ
⌊ I , i ⌋ = I

ind : ∀ {Σ X} → (I : Interp Σ X) → X → Δ ⌊ I ⌋
ind (I , i) = i

ind² : ∀ {Σ X} → (I : Interp Σ X) → (X × X) → (Δ ⌊ I ⌋ × Δ ⌊ I ⌋)
ind² I (x , y) = (ind I x , ind I y)

_*_ : ∀ {Σ X Y} → (Y → X) → Interp Σ X → Interp Σ Y
f * I = (⌊ I ⌋ , λ x → ind I (f x))

emp : ∀ {Σ} → Interp Σ False
emp = (emp′ , id)

data Surjective {Σ X} (I : Interp Σ X) : Set where
  surj : (∀ x → ∃ λ y → ⌊ I ⌋ ⊨ x ≈ ind I y) → (I ∈ Surjective)

ind⁻¹ : ∀ {Σ X} {I : Interp Σ X} → (I ∈ Surjective) → (Δ ⌊ I ⌋ → X)
ind⁻¹ (surj i) x = proj₁ (i x)

surj✓ : ∀ {Σ X} {I : Interp Σ X} (I∈Surj : I ∈ Surjective) → ∀ x → (⌊ I ⌋ ⊨ x ≈ ind I (ind⁻¹ I∈Surj x))
surj✓ (surj i) x = proj₂ (i x)
