open import Data.Product using ( _,_ )
open import Relation.Nullary using ( yes ; no )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox.Interp using 
  ( Interp ; _,_ ; ⌊_⌋ ; ind ; ind² ; Surjective ; surj ; ind⁻¹ ; surj✓ )
open import Web.Semantic.DL.ABox.Interp.Morphism using ( _≲_ ; _,_ ; ≲⌊_⌋ ; ≲-resp-ind ; _≋_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox.Interp using ( interp ; _⊨_≈_ ; ≈-refl ; ≈-sym ; ≈-trans ; con ; rol ; con-≈ ; rol-≈ )
open import Web.Semantic.DL.TBox.Interp.Morphism using ( morph ; ≲-image ; ≲-resp-≈ ; ≲-resp-con ; ≲-resp-rol )
open import Web.Semantic.Util using ( _∘_ ; ExclMiddle₁ ; ExclMiddle ; smaller-excl-middle ; id ; □ ; is ; is! ; is✓ )

-- Note that this construction uses excluded middle
-- (for cardinality reasons, to embed a large set in a small set).

module Web.Semantic.DL.ABox.Interp.Meet ( excl-middle₁ : ExclMiddle₁ ) { Σ : Signature } { X : Set } where

-- This constructs the meet of a set of interpretations,
-- which is the greatest lower bound on surjective interpretations

meet : (Interp Σ X → Set) → Interp Σ X
meet Is = 
  ( interp X 
    (λ x y → □ (is (excl-middle₁ (∀ I → (I ∈ Is) → 
      (⌊ I ⌋ ⊨ ind I x ≈ ind I y)))))
    (λ {x} → is! (λ I I∈Is → 
      ≈-refl ⌊ I ⌋)) 
    (λ {x} {y} x≈y → is! (λ I I∈Is → 
      ≈-sym ⌊ I ⌋ (is✓ x≈y I I∈Is))) 
    (λ {x} {y} {z} x≈y y≈z → is! (λ I I∈Is → 
      ≈-trans ⌊ I ⌋ (is✓ x≈y I I∈Is) (is✓ y≈z I I∈Is)))
    (λ c x → □ (is (excl-middle₁ (∀ I → (I ∈ Is) → 
      (ind I x ∈ con ⌊ I ⌋ c)))))
    (λ r xy → □ (is (excl-middle₁ (∀ I → (I ∈ Is) →
      ind² I xy ∈ rol ⌊ I ⌋ r))))
    (λ {x} {y} c x∈c x≈y → is! (λ I I∈Is → 
      con-≈ ⌊ I ⌋ c (is✓ x∈c I I∈Is) (is✓ x≈y I I∈Is)))
    (λ {w} {x} {y} {z} r w≈x xy∈r y≈z → is! (λ I I∈Is →
      rol-≈ ⌊ I ⌋ r (is✓ w≈x I I∈Is) (is✓ xy∈r I I∈Is) (is✓ y≈z I I∈Is)))
  , id )

-- meets are surjective

meet-surj : ∀ Is → (meet Is ∈ Surjective)
meet-surj Is = surj (λ x → (x , ≈-refl ⌊ meet Is ⌋))

-- meets are lower bounds

meet-lb : ∀ Is I → (I ∈ Is) → (meet Is ≲ I)
meet-lb Is I I∈Is = 
  ( morph (ind I) 
      (λ x≈y → is✓ x≈y I I∈Is) 
      (λ x∈⟦c⟧ → is✓ x∈⟦c⟧ I I∈Is) 
      (λ xy∈⟦r⟧ → is✓ xy∈⟦r⟧ I I∈Is)
  , λ x → ≈-refl ⌊ I ⌋ )

-- meets are greatest lower bounds on surjective interpretations

meet-glb : ∀ Is J → (J ∈ Surjective) → (∀ I → (I ∈ Is) → (J ≲ I)) → (J ≲ meet Is)
meet-glb Is J J∈Surj J≲Is = 
  ( morph (ind⁻¹ J∈Surj) 
      (λ {x} {y} x≈y → is! (λ I I∈Is →
        ≈-trans ⌊ I ⌋ (≈-sym ⌊ I ⌋ (lemma I I∈Is x)) (≈-trans ⌊ I ⌋ (≲-resp-≈ ≲⌊ J≲Is I I∈Is ⌋ x≈y) (lemma I I∈Is y))))
      (λ {c} {x} x∈⟦c⟧ → is! (λ I I∈Is → 
        con-≈ ⌊ I ⌋ c (≲-resp-con ≲⌊ J≲Is I I∈Is ⌋ x∈⟦c⟧) (lemma I I∈Is x)))
      (λ {r} {x} {y} xy∈⟦r⟧ → is! (λ I I∈Is → 
        rol-≈ ⌊ I ⌋ r (≈-sym ⌊ I ⌋ (lemma I I∈Is x)) (≲-resp-rol ≲⌊ J≲Is I I∈Is ⌋ xy∈⟦r⟧) (lemma I I∈Is y)))
  , λ x → is! (λ I I∈Is → 
      ≈-trans ⌊ I ⌋ (≈-sym ⌊ I ⌋ (lemma I I∈Is (ind J x))) (≲-resp-ind (J≲Is I I∈Is) x)) ) where

  lemma : ∀ I I∈Is x → ⌊ I ⌋ ⊨ ≲-image ≲⌊ J≲Is I I∈Is ⌋ x ≈ ind I (ind⁻¹ J∈Surj x)
  lemma I I∈Is x = 
    ≈-trans ⌊ I ⌋ (≲-resp-≈ ≲⌊ J≲Is I I∈Is ⌋ (surj✓ J∈Surj x)) 
      (≲-resp-ind (J≲Is I I∈Is) (ind⁻¹ J∈Surj x))

-- Mediating morphisms for meets are unique

meet-uniq : ∀ Is (I : Interp Σ X) → (I ∈ Is) → (J≲₁I J≲₂I : meet Is ≲ I) → (J≲₁I ≋ J≲₂I)
meet-uniq Is I I∈Is J≲₁I J≲₂I x = ≈-trans ⌊ I ⌋ (≲-resp-ind J≲₁I x) (≈-sym ⌊ I ⌋ (≲-resp-ind J≲₂I x))
