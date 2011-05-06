open import Data.Bool using ( Bool ; true ; false ; if_then_else_ )
open import Data.Empty using ( ⊥-elim )
open import Data.Product using ( _×_ ; _,_ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Relation.Unary using ( _∈_ ; _∉_ )
open import Web.Semantic.DL.Concept using ( neg )
open import Web.Semantic.DL.Concept.Model using ( _⟦_⟧₁ ; neg-sound )
open import Web.Semantic.DL.Concept.Skolemization using
  ( CSkolems ; cskolem ; cskolem-sound )
open import Web.Semantic.DL.FOL using
  ( Formula ; true ; false ; _∧_ ; _∈₁_ ; _∈₂_ ; _∼_ ; ∀₁ )
open import Web.Semantic.DL.FOL.Model using ( _⊨f_ )
open import Web.Semantic.DL.Role.Skolemization using
  ( rskolem ; rskolem⇒ ; rskolem-sound ; rskolem⇒-sound )
open import Web.Semantic.DL.Role.Model using ( _⟦_⟧₂ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using
  ( TBox ; ε ; _,_ ;_⊑₁_ ; _⊑₂_ ; Dis ; Ref ; Irr ; Tra )
open import Web.Semantic.DL.TBox.Model using ( _⊨t_ )
open import Web.Semantic.Util using ( True ; tt )

module Web.Semantic.DL.TBox.Skolemization {Σ : Signature} where

TSkolems : Set → TBox Σ → Set
TSkolems Δ ε = True
TSkolems Δ (T , U) = (TSkolems Δ T) × (TSkolems Δ U)
TSkolems Δ (C ⊑₁ D) = (Δ → Bool) × (CSkolems Δ (neg C)) × (CSkolems Δ D)
TSkolems Δ (Q ⊑₂ R) = True
TSkolems Δ (Dis Q R) = True
TSkolems Δ (Ref R) = True
TSkolems Δ (Irr R) = True
TSkolems Δ (Tra R) = True

tskolem : ∀ {Δ} T → (TSkolems Δ T) → Formula Σ Δ
tskolem ε Φ = true
tskolem (T , U) (Φ , Ψ) = (tskolem T Φ) ∧ (tskolem U Ψ)
tskolem (C ⊑₁ D) (φ , Φ , Ψ) = ∀₁ λ x → 
  if (φ x) then (cskolem (neg C) Φ x) else (cskolem D Ψ x)
tskolem (Q ⊑₂ R) Φ = ∀₁ λ x → ∀₁ λ y → 
  rskolem⇒ Q x y (rskolem R x y)
tskolem (Dis Q R) Φ = ∀₁ λ x → ∀₁ λ y →
  rskolem⇒ Q x y (rskolem⇒ R x y false)
tskolem (Ref R) Φ = ∀₁ λ x →
  rskolem R x x
tskolem (Irr R) Φ = ∀₁ λ x →
  rskolem⇒ R x x false
tskolem (Tra R) Φ = ∀₁ λ x → ∀₁ λ y → ∀₁ λ z → 
  rskolem⇒ R x y (rskolem⇒ R y z (rskolem R x z))

tskolem-sound : ∀ I T Φ → (I ⊨f tskolem T Φ) → (I ⊨t T)
tskolem-sound I ε Φ _ = tt
tskolem-sound I (T , U) (Φ , Ψ) (I⊨T , I⊨U) = 
  (tskolem-sound I T Φ I⊨T , tskolem-sound I U Ψ I⊨U)
tskolem-sound I (C ⊑₁ D) (φ , Φ , Ψ) I⊨C⊑D = lemma where
  lemma : ∀ {x} → (x ∈ I ⟦ C ⟧₁) → (x ∈ I ⟦ D ⟧₁)
  lemma {x} x∈⟦C⟧ with φ x | I⊨C⊑D x
  lemma {x} x∈⟦C⟧ | true  | x∈⟦¬C⟧ = 
    ⊥-elim (neg-sound I C (cskolem-sound I (neg C) Φ x x∈⟦¬C⟧) x∈⟦C⟧)
  lemma {x} x∈⟦C⟧ | false | x∈⟦D⟧  = 
    cskolem-sound I D Ψ x x∈⟦D⟧
tskolem-sound I (Q ⊑₂ R) Φ I⊨Q⊑R = lemma where
  lemma : ∀ {xy} → (xy ∈ I ⟦ Q ⟧₂) → (xy ∈ I ⟦ R ⟧₂)
  lemma {x , y} xy∈⟦Q⟧ = 
    rskolem-sound I R x y (rskolem⇒-sound I Q x y _ (I⊨Q⊑R x y) xy∈⟦Q⟧)
tskolem-sound I (Dis Q R) Φ I⊨DisQR = lemma where
  lemma : ∀ {xy} → (xy ∈ I ⟦ Q ⟧₂) → (xy ∉ I ⟦ R ⟧₂)
  lemma {x , y} xy∈⟦Q⟧ = 
    rskolem⇒-sound I R x y _ (rskolem⇒-sound I Q x y _ (I⊨DisQR x y) xy∈⟦Q⟧)
tskolem-sound I (Ref R) Φ I⊨RefR = λ x → rskolem-sound I R x x (I⊨RefR x)
tskolem-sound I (Irr R) Φ I⊨IrrR = λ x → rskolem⇒-sound I R x x _ (I⊨IrrR x)
tskolem-sound I (Tra R) Φ I⊨TraR = 
  λ {x} {y} {z} xy∈⟦R⟧ yz∈⟦R⟧ → rskolem-sound I R x z 
    (rskolem⇒-sound I R y z _ (rskolem⇒-sound I R x y _ (I⊨TraR x y z) xy∈⟦R⟧) yz∈⟦R⟧)