open import Data.Product using ( _×_ ; _,_ ; swap )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Relation.Nullary using ( ¬_ ; yes ; no )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox ; ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ )
open import Web.Semantic.DL.ABox.Interp using
  ( Interp ; ⌊_⌋ ; ind ; ind⁻¹ ; Surjective ; surj✓ )
open import Web.Semantic.DL.ABox.Interp.Morphism using
  ( _≲_ ; _≃_ ; _,_ ; ≲⌊_⌋ ; ≲-resp-ind )
open import Web.Semantic.DL.ABox.Interp.Meet using
  ( meet ; meet-lb ; meet-glb ; meet-uniq ; meet-surj )
open import Web.Semantic.DL.ABox.Model using ( _⊨a_ )
open import Web.Semantic.DL.Concept using 
  ( Concept ; ⟨_⟩ ; ¬⟨_⟩ ; ⊤ ; ⊥ ; _⊔_ ; _⊓_ ; ∀[_]_ ; ∃⟨_⟩_ ; ≤1 ; >1 ; neg )
open import Web.Semantic.DL.Concept.Model using
  ( _⟦_⟧₁ ; neg-sound ; neg-complete )
open import Web.Semantic.DL.Integrity.Closed using
  ( Mediated₀ ; Initial₀ ; sur_⊨₀_ ; _,_ )
open import Web.Semantic.DL.Integrity.Closed.Alternate using 
  ( _⊫_∼_ ; _⊫_∈₁_ ; _⊫_∈₂_ ; _⊫t_ ; _⊫a_ ; _⊫k_
  ; eq ; rel ; rev ; +atom ; -atom ; top ; inj₁ ; inj₂
  ; all ; ex ; uniq ; ¬uniq ; cn ; rl ; tr ; ε ; _,_ )
open import Web.Semantic.DL.KB using ( KB ; tbox ; abox )
open import Web.Semantic.DL.KB.Model using ( _⊨_ ; Interps ; ⊨-resp-≃ )
open import Web.Semantic.DL.Role using ( Role ; ⟨_⟩ ; ⟨_⟩⁻¹ )
open import Web.Semantic.DL.Role.Model using ( _⟦_⟧₂ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox ; ε ; _,_ ; _⊑₁_ ; _⊑₂_ ; Tra )
open import Web.Semantic.DL.TBox.Interp using ( _⊨_≈_ ; ≈-sym ; ≈-trans )
open import Web.Semantic.DL.TBox.Interp.Morphism using ( ≲-resp-≈ ; iso )
open import Web.Semantic.DL.TBox.Model using ( _⊨t_ )
open import Web.Semantic.Util using 
  ( ExclMiddle ; ExclMiddle₁ ; smaller-excl-middle ; is! ; is✓ ; tt ; elim )

module Web.Semantic.DL.Integrity.Closed.Properties
  (excl-middle₁ : ExclMiddle₁) {Σ : Signature} {X : Set} where

-- The two definitions of closed-world integrity coincide for surjective interpretations.
-- Note that this requires excluded middle, as the alternate definition assumes a classical logic,
-- for example interpreting C ⊑ D as (¬ C ⊔ D) being a tautology.

min : KB Σ X → Interp Σ X
min K = meet excl-middle₁ (Interps K)

excl-middle : ExclMiddle
excl-middle = smaller-excl-middle excl-middle₁

sound∼ : ∀ K x y → (K ⊫ x ∼ y) → (⌊ min K ⌋ ⊨ x ≈ y)
sound∼ K x y (eq K⊫x∼y) = is! K⊫x∼y

complete∼ : ∀ K x y → (⌊ min K ⌋ ⊨ x ≈ y) → (K ⊫ x ∼ y)
complete∼ K x y x≈y = eq (is✓ x≈y)

sound₂ : ∀ K R xy → (K ⊫ xy ∈₂ R) → (xy ∈ ⌊ min K ⌋ ⟦ R ⟧₂)
sound₂ K ⟨ r ⟩   (x , y) (rel K⊫xy∈r) = is! K⊫xy∈r
sound₂ K ⟨ r ⟩⁻¹ (x , y) (rev K⊫yx∈r) = is! K⊫yx∈r

complete₂ : ∀ K R xy → (xy ∈ ⌊ min K ⌋ ⟦ R ⟧₂) → (K ⊫ xy ∈₂ R)
complete₂ K ⟨ r ⟩   (x , y) xy∈⟦r⟧ = rel (is✓ xy∈⟦r⟧)
complete₂ K ⟨ r ⟩⁻¹ (x , y) yx∈⟦r⟧ = rev (is✓ yx∈⟦r⟧)

sound₁ : ∀ K C x → (K ⊫ x ∈₁ C) → (x ∈ ⌊ min K ⌋ ⟦ C ⟧₁)
sound₁ K ⟨ c ⟩ x (+atom K⊨x∈c) =
  is! K⊨x∈c
sound₁ K ¬⟨ c ⟩ x (-atom K⊭x∈c) =
  λ x∈⟦c⟧ → K⊭x∈c (is✓ x∈⟦c⟧)
sound₁ K ⊤ x top = tt
sound₁ K ⊥ x ()
sound₁ K (C ⊓ D) x (K⊫x∈C , K⊫x∈D) =
  (sound₁ K C x K⊫x∈C , sound₁ K D x K⊫x∈D)
sound₁ K (C ⊔ D) x (inj₁ K⊫x∈C) =
  inj₁ (sound₁ K C x K⊫x∈C)
sound₁ K (C ⊔ D) x (inj₂ K⊫x∈D) =
  inj₂ (sound₁ K D x K⊫x∈D)
sound₁ K (∀[ R ] C) x (all K⊫x∈∀RC) =
  λ y xy∈⟦R⟧ → sound₁ K C y (K⊫x∈∀RC y (complete₂ K R _ xy∈⟦R⟧))
sound₁ K (∃⟨ R ⟩ C) x (ex y K⊫xy∈R K⊫y∈C) =
  (y , sound₂ K R _ K⊫xy∈R , sound₁ K C y K⊫y∈C)
sound₁ K (≤1 R) x (uniq K⊫x∈≤1R) =
  λ y z xy∈⟦R⟧ xz∈⟦R⟧ → sound∼ K y z 
    (K⊫x∈≤1R y z (complete₂ K R _ xy∈⟦R⟧) (complete₂ K R _ xz∈⟦R⟧))
sound₁ K (>1 R) x (¬uniq y z K⊫xy∈R K⊫xz∈R K⊯y∼z) =
  ( y , z , sound₂ K R _ K⊫xy∈R , sound₂ K R _ K⊫xz∈R
  , λ y≈z → K⊯y∼z (complete∼ K y z y≈z) )

complete₁ : ∀ K C x → (x ∈ ⌊ min K ⌋ ⟦ C ⟧₁) → (K ⊫ x ∈₁ C)
complete₁ K ⟨ c ⟩ x x∈⟦c⟧ =
  +atom (is✓ x∈⟦c⟧)
complete₁ K ¬⟨ c ⟩ x x∉⟦c⟧ =
  -atom (λ K⊫x∈c → x∉⟦c⟧ (is! K⊫x∈c))
complete₁ K ⊤ x x∈⟦C⟧ =
  top
complete₁ K ⊥ x ()
complete₁ K (C ⊓ D) x (x∈⟦C⟧ , x∈⟦D⟧) =
  (complete₁ K C x x∈⟦C⟧ , complete₁ K D x x∈⟦D⟧)
complete₁ K (C ⊔ D) x (inj₁ x∈⟦C⟧) =
  inj₁ (complete₁ K C x x∈⟦C⟧)
complete₁ K (C ⊔ D) x (inj₂ x∈⟦D⟧) =
  inj₂ (complete₁ K D x x∈⟦D⟧)
complete₁ K (∀[ R ] C) x x∈⟦∀RC⟧ =
  all (λ y K⊫xy∈R → complete₁ K C y (x∈⟦∀RC⟧ y (sound₂ K R _ K⊫xy∈R)))
complete₁ K (∃⟨ R ⟩ C) x (y , xy∈⟦R⟧ , y∈⟦C⟧) =
  ex y (complete₂ K R (x , y) xy∈⟦R⟧) (complete₁ K C y y∈⟦C⟧)
complete₁ K (≤1 R) x x∈⟦≤1R⟧ =
  uniq (λ y z K⊫xy∈R K⊫xz∈R → complete∼ K y z 
    (x∈⟦≤1R⟧ y z (sound₂ K R _ K⊫xy∈R) (sound₂ K R _ K⊫xz∈R)))
complete₁ K (>1 R) x (y , z , xy∈⟦R⟧ , xz∈⟦R⟧ , y≉z) =
  ¬uniq y z (complete₂ K R _ xy∈⟦R⟧) (complete₂ K R _ xz∈⟦R⟧)
    (λ K⊫y∼z → y≉z (sound∼ K y z K⊫y∼z))

⊫-impl-min⊨ : ∀ K L → (K ⊫k L) → (min K ⊨ L)
⊫-impl-min⊨ K L (K⊫T , K⊫A) = ( J⊨T K⊫T , J⊨A K⊫A ) where

  J : Interp Σ X
  J = min K

  J⊨T : ∀ {T} → (K ⊫t T) → (⌊ J ⌋ ⊨t T)
  J⊨T ε = tt
  J⊨T (K⊫T , K⊫U) = (J⊨T K⊫T , J⊨T K⊫U)
  J⊨T (tr R K⊫TraR) =
    λ {x} {y} {z} xy∈⟦R⟧ yz∈⟦R⟧ → 
      sound₂ K R (x , z) (K⊫TraR x y z 
        (complete₂ K R (x , y) xy∈⟦R⟧) (complete₂ K R (y , z) yz∈⟦R⟧))
  J⊨T (rl Q R K⊫Q⊑R) = 
    λ {xy} xy∈⟦Q⟧ → sound₂ K R xy (K⊫Q⊑R xy (complete₂ K Q xy xy∈⟦Q⟧))
  J⊨T (cn C D K⊫C⊑D) = λ {x} → lemma x (K⊫C⊑D x) where

    lemma : ∀ x → (K ⊫ x ∈₁ (neg C ⊔ D)) → 
      (x ∈ ⌊ J ⌋ ⟦ C ⟧₁) → (x ∈ ⌊ J ⌋ ⟦ D ⟧₁)
    lemma x (inj₁ K⊫x∈¬C) x∈⟦C⟧ = 
      elim (neg-sound ⌊ J ⌋ {x} C (sound₁ K (neg C) x K⊫x∈¬C) x∈⟦C⟧)
    lemma x (inj₂ K⊫x∈D) x∈⟦C⟧ =
      sound₁ K D x K⊫x∈D

  J⊨A : ∀ {A} → (K ⊫a A) → (J ⊨a A)
  J⊨A ε = tt
  J⊨A (K⊫A , K⊫B) = (J⊨A K⊫A , J⊨A K⊫B)
  J⊨A (eq x y K⊫x∼y) = sound∼ K x y K⊫x∼y
  J⊨A (rl (x , y) r K⊫xy∈r) = sound₂ K ⟨ r ⟩ (x , y) K⊫xy∈r
  J⊨A (cn x c K⊫x∈c) = sound₁ K ⟨ c ⟩ x K⊫x∈c

min⊨-impl-⊫ : ∀ K L → (min K ⊨ L) → (K ⊫k L)
min⊨-impl-⊫ K L (J⊨T , J⊨A) = 
  ( K⊫T (tbox L) J⊨T ,  K⊫A (abox L) J⊨A ) where

  J : Interp Σ X
  J = min K

  K⊫T : ∀ T → (⌊ J ⌋ ⊨t T) → (K ⊫t T)
  K⊫T ε J⊨ε = ε
  K⊫T (T , U) (J⊨T , J⊨U) = (K⊫T T J⊨T , K⊫T U J⊨U)
  K⊫T (Tra R) J⊨TrR = 
    tr R (λ x y z K⊫xy∈R K⊫yz∈R → 
      complete₂ K R (x , z) (J⊨TrR 
        (sound₂ K R (x , y) K⊫xy∈R) (sound₂ K R (y , z) K⊫yz∈R)))
  K⊫T (Q ⊑₂ R) J⊨Q⊑R =
    rl Q R (λ xy K⊫xy∈Q → complete₂ K R xy (J⊨Q⊑R (sound₂ K Q xy K⊫xy∈Q)))
  K⊫T (C ⊑₁ D) J⊨C⊑D = cn C D lemma where

    lemma : ∀ x → (K ⊫ x ∈₁ neg C ⊔ D)
    lemma x with excl-middle (x ∈ ⌊ J ⌋ ⟦ C ⟧₁)
    lemma x | yes x∈⟦C⟧ = 
      inj₂ (complete₁ K D x (J⊨C⊑D x∈⟦C⟧))
    lemma x | no  x∉⟦C⟧ = 
      inj₁ (complete₁ K (neg C) x (neg-complete excl-middle ⌊ J ⌋ C x∉⟦C⟧))

  K⊫A : ∀ A → (J ⊨a A) → (K ⊫a A)
  K⊫A ε J⊨ε = ε
  K⊫A (A , B) (J⊨A , J⊨B) = (K⊫A A J⊨A , K⊫A B J⊨B)
  K⊫A (x ∼ y) x≈y = eq x y (complete∼ K x y x≈y)
  K⊫A (x ∈₁ c) x∈⟦c⟧ = cn x c (complete₁ K ⟨ c ⟩ x x∈⟦c⟧)
  K⊫A ((x , y) ∈₂ r) xy∈⟦r⟧ = rl (x , y) r (complete₂ K ⟨ r ⟩ (x , y) xy∈⟦r⟧)

min-med : ∀ (K : KB Σ X) J → (J ⊨ K) → Mediated₀ (min K) J
min-med K J J⊨K = (meet-lb excl-middle₁ (Interps K) J J⊨K , meet-uniq excl-middle₁ (Interps K) J J⊨K)

min-init : ∀ (K : KB Σ X) → (K ⊫k K) → (min K ∈ Initial₀ K)
min-init K K⊫K = ( ⊫-impl-min⊨ K K K⊫K , min-med K)

min-uniq : ∀ (I : Interp Σ X) (K : KB Σ X) → (I ∈ Surjective) → (I ∈ Initial₀ K) → (I ≃ min K)
min-uniq I K I∈Surj (I⊨K , I-med) = 
  ( iso 
      ≲⌊ meet-glb excl-middle₁ (Interps K) I I∈Surj lemma₁ ⌋ 
      ≲⌊ meet-lb excl-middle₁ (Interps K) I I⊨K ⌋ 
      (λ x → ≈-sym ⌊ I ⌋ (surj✓ I∈Surj x)) 
      (λ x → is! (lemma₂ x))
  , λ x → is! (lemma₂ x)) where

  lemma₁ : ∀ J J⊨K → I ≲ J
  lemma₁ J J⊨K with I-med J J⊨K
  lemma₁ J J⊨K | (I≲J , I≲J-uniq) = I≲J

  lemma₂ : ∀ x J J⊨K → ⌊ J ⌋ ⊨ ind J (ind⁻¹ I∈Surj (ind I x)) ≈ ind J x
  lemma₂ x J J⊨K =
    ≈-trans ⌊ J ⌋ (≈-sym ⌊ J ⌋ (≲-resp-ind (lemma₁ J J⊨K) (ind⁻¹ I∈Surj (ind I x)))) 
      (≈-trans ⌊ J ⌋ (≲-resp-≈ ≲⌊ lemma₁ J J⊨K ⌋ (≈-sym ⌊ I ⌋ (surj✓ I∈Surj (ind I x))))
        (≲-resp-ind (lemma₁ J J⊨K) x))

⊫-impl-⊨₀ : ∀ (KB₁ KB₂ : KB Σ X) → (KB₁ ⊫k KB₁) → (KB₁ ⊫k KB₂) → (sur KB₁ ⊨₀ KB₂)
⊫-impl-⊨₀ KB₁ KB₂ KB₁⊫KB₁ KB₁⊫KB₂ = 
  ( min KB₁
  , meet-surj excl-middle₁ (Interps KB₁)
  , min-init KB₁ KB₁⊫KB₁
  , ⊫-impl-min⊨ KB₁ KB₂ KB₁⊫KB₂ )

⊨₀-impl-⊫₁ : ∀ (KB₁ KB₂ : KB Σ X) → (sur KB₁ ⊨₀ KB₂) → (KB₁ ⊫k KB₁)
⊨₀-impl-⊫₁ KB₁ KB₂ (I , I∈Surj , (I⊨KB₁ , I-med) , I⊨KB₂) =
  min⊨-impl-⊫ KB₁ KB₁ (⊨-resp-≃ (min-uniq I KB₁ I∈Surj (I⊨KB₁ , I-med)) KB₁ I⊨KB₁)

⊨₀-impl-⊫₂ : ∀ (KB₁ KB₂ : KB Σ X) → (sur KB₁ ⊨₀ KB₂) → (KB₁ ⊫k KB₂)
⊨₀-impl-⊫₂ KB₁ KB₂ (I , I∈Surj , I-init , I⊨KB₂) = 
  min⊨-impl-⊫ KB₁ KB₂ (⊨-resp-≃ (min-uniq I KB₁ I∈Surj I-init) KB₂ I⊨KB₂)
