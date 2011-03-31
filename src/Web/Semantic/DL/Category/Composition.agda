open import Data.Product using ( ∃ ; _×_ ; _,_ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox ; ⟨ABox⟩ ; _,_ )
open import Web.Semantic.DL.ABox.Interp using ( Interp ; _,_ ; _*_ )
open import Web.Semantic.DL.ABox.Interp.Morphism using ( _≲_ ; _,_ ; _**_ ; _≋_ )
open import Web.Semantic.DL.ABox.Model using ( _⊨a_ ; ⊨a-resp-≲ ; ⟨Abox⟩-resp-⊨ ; *-resp-⟨ABox⟩ )
open import Web.Semantic.DL.Category.Morphism using ( _⇒_ ; _,_ ; BN ; impl )
open import Web.Semantic.DL.Category.Object using ( Object ; _,_ ; IN ; iface )
open import Web.Semantic.DL.KB using ( KB ; _,_ )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.KB.Initial using ( Unique ; Mediated ; Mediator ; Initial ; _⊕_⊨_ ; _>>_ ; _,_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox ; _,_ )
open import Web.Semantic.DL.TBox.Interp using ( Δ ; _⊨_≈_ ; ≈-refl ; ≈-sym ; ≈-trans )
open import Web.Semantic.DL.TBox.Interp.Morphism using ( ≲-image ; ≲-trans ; ≲-resp-≈ )
open import Web.Semantic.Util using ( _⊕_⊕_ ; inode ; bnode ; enode ; left ; right ; merge ; _∘_ )

module Web.Semantic.DL.Category.Composition {Σ : Signature} {S T : TBox Σ} where

_⟫_ : ∀ {V W X Y Z} → ABox Σ (X ⊕ V ⊕ Y) → ABox Σ (Y ⊕ W ⊕ Z) →
  ABox Σ (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z)
F ⟫ G = (⟨ABox⟩ left F , ⟨ABox⟩ right G)

pipe : ∀ {V W X Y Z} →
  (J : Interp Σ (X ⊕ V ⊕ Y)) → (K : Interp Σ (Y ⊕ W ⊕ Z)) →
    (enode * J ≲ inode * K) → (Interp Σ (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z))
pipe (J , j) (K , k) (J≲K , j≲k) = (K , merge (≲-image J≲K ∘ j) k)

pipe-≳ : ∀ {V W X Y Z} → (I : Interp Σ X) → 
  (J : Interp Σ (X ⊕ V ⊕ Y)) → (K : Interp Σ (Y ⊕ W ⊕ Z)) →
    (I≲J : I ≲ inode * J) → (J≲K : enode * J ≲ inode * K) → 
      (I ≲ inode * (pipe J K J≲K))
pipe-≳ (I , i) (J , j) (K , k) (I≲J , i≲j) (J≲K , j≲k) = 
  (≲-trans I≲J J≲K , λ x → ≲-resp-≈ J≲K (i≲j x))

pipe-⟫ : ∀ {V W X Y Z} →
  (J : Interp Σ (X ⊕ V ⊕ Y)) → (K : Interp Σ (Y ⊕ W ⊕ Z)) →
    (J≲K : enode * J ≲ inode * K) → 
      ∀ F G → (J ⊨a F) → (K ⊨a G) → (pipe J K J≲K ⊨a F ⟫ G)
pipe-⟫ (J , j) (K , k) (J≲K , j≲k) F G J⊨F K⊨G = 
  (⟨Abox⟩-resp-⊨ left lemma₁ F K⊨F , ⟨Abox⟩-resp-⊨ right lemma₂ G K⊨G) where

  K⊨F : (K , (≲-image J≲K ∘ j)) ⊨a F
  K⊨F = ⊨a-resp-≲ (J≲K , λ x → ≈-refl K) F J⊨F

  lemma₁ : ∀ x → (K ⊨ ≲-image J≲K (j x) ≈ merge (≲-image J≲K ∘ j) k (left x))
  lemma₁ (inode x) = ≈-refl K
  lemma₁ (bnode v) = ≈-refl K
  lemma₁ (enode y) = j≲k y

  lemma₂ : ∀ x → (K ⊨ k x ≈ merge (≲-image J≲K ∘ j) k (right x))
  lemma₂ (inode x) = ≈-refl K
  lemma₂ (bnode v) = ≈-refl K
  lemma₂ (enode y) = ≈-refl K

pipe-≲ : ∀ {V W X Y Z} → 
  (J : Interp Σ (X ⊕ V ⊕ Y)) → (K : Interp Σ (Y ⊕ W ⊕ Z)) →
    (L : Interp Σ (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z)) → 
      (J≲K : enode * J ≲ inode * K) → (J≲L : J ≲ left * L) → 
        (K≲L : K ≲ right * L) → (enode ** J≲L ≋ J≲K >> K≲L) → 
          (pipe J K J≲K ≲ L)
pipe-≲ (J , j) (K , k) (L , l) (J≲K , j≲k) (J≲L , j≲l) (K≲L , k≲l) J≲L≋J≲K≲L =
  (K≲L , lemma) where

  lemma : ∀ x → L ⊨ ≲-image K≲L (merge (≲-image J≲K ∘ j) k x) ≈ l x
  lemma (inode x) = 
    ≈-trans L (≈-sym L (J≲L≋J≲K≲L (j (inode x)))) (j≲l (inode x))
  lemma (bnode (inode v)) = 
    ≈-trans L (≈-sym L (J≲L≋J≲K≲L (j (bnode v)))) (j≲l (bnode v))
  lemma (bnode (bnode y)) = k≲l (inode y)
  lemma (bnode (enode w)) = k≲l (bnode w)
  lemma (enode z) = k≲l (enode z)

pipe-≋ : ∀ {V W X Y Z} → (I : Interp Σ X) → 
  (J : Interp Σ (X ⊕ V ⊕ Y)) → (K : Interp Σ (Y ⊕ W ⊕ Z)) →
    (L : Interp Σ (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z)) → 
      (I≲J : I ≲ inode * J) → (I≲L : I ≲ inode * L) → 
        (J≲K : enode * J ≲ inode * K) → (J≲L : J ≲ left * L) → 
          (K≲L : K ≲ right * L) →
            (I≲L ≋ I≲J >> J≲L) → (J≲L≋J≲K≲L : enode ** J≲L ≋ J≲K >> K≲L) → 
              (I≲L ≋ pipe-≳ I J K I≲J J≲K >> pipe-≲ J K L J≲K J≲L K≲L J≲L≋J≲K≲L)
pipe-≋ (I , i) (J , j) (K , k) (L , l) 
  (I≲J , i≲j) (I≲L , i≲l) (J≲K , j≲k) (J≲L , j≲l) (K≲L , k≲l)
    I≲L≋I≲J≲L J≲L≋J≲K≲L = 
      λ x → ≈-trans L (I≲L≋I≲J≲L x) 
        (J≲L≋J≲K≲L (≲-image I≲J x))

pipe-uniq : ∀ {V W X Y Z} → (I : Interp Σ X) → 
  (J : Interp Σ (X ⊕ V ⊕ Y)) → (K : Interp Σ (Y ⊕ W ⊕ Z)) →
    (L : Interp Σ (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z)) → 
      (I≲J : I ≲ inode * J) → (I≲L : I ≲ inode * L) → 
        (J≲K : enode * J ≲ inode * K) → (J≲L : J ≲ left * L) → 
          (K≲L : K ≲ right * L) →
            (J≲L≋J≲K≲L : enode ** J≲L ≋ J≲K >> K≲L) →
              (Unique I J (left * L) I≲J I≲L J≲L) → 
                (Unique (enode * J) K (right * L) J≲K (enode ** J≲L) K≲L) → 
                  (Unique I (pipe J K J≲K) L (pipe-≳ I J K I≲J J≲K) 
                     I≲L (pipe-≲ J K L J≲K J≲L K≲L J≲L≋J≲K≲L))
pipe-uniq (I , i) (J , j) (K , k) (L , l) 
  (I≲J , i≲j) (I≲L , i≲l) (J≲K , j≲k) (J≲L , j≲l) (K≲L , k≲l)
    J≲L≋J≲K≲L J-uniq K-uniq
      (K≲L′ , k≲l′) I≲L≋I≲K≲L′ = 
        K-uniq (K≲L′ , lemma₂)
          (J-uniq (≲-trans J≲K K≲L′ , lemma₁) I≲L≋I≲K≲L′) where

  lemma₁ : ∀ x → L ⊨ ≲-image K≲L′ (≲-image J≲K (j x)) ≈ l (left x)
  lemma₁ (inode x) = k≲l′ (inode x)
  lemma₁ (bnode v) = k≲l′ (bnode (inode v))
  lemma₁ (enode y) = ≈-trans L (≲-resp-≈ K≲L′ (j≲k y)) (k≲l′ (bnode (bnode y)))

  lemma₂ : ∀ x → L ⊨ ≲-image K≲L′ (k x) ≈ l (right x)
  lemma₂ (inode y) = k≲l′ (bnode (bnode y))
  lemma₂ (bnode w) = k≲l′ (bnode (enode w))
  lemma₂ (enode z) = k≲l′ (enode z)

pipe-med″ : ∀ {V W X Y Z} → (I : Interp Σ X) → 
  (J : Interp Σ (X ⊕ V ⊕ Y)) → (K : Interp Σ (Y ⊕ W ⊕ Z)) →
    (I≲J : I ≲ inode * J) → (J≲K : enode * J ≲ inode * K) → 
      (L : Interp Σ (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z)) → (I≲L : I ≲ inode * L) → 
        (J≲L : J ≲ left * L) → (I≲L ≋ I≲J >> J≲L) →
          (Unique I J (left * L) I≲J I≲L J≲L) → 
            Mediated (enode * J) K (right * L) J≲K (enode ** J≲L) → 
              Mediated I (pipe J K J≲K) L (pipe-≳ I J K I≲J J≲K) I≲L
pipe-med″ I J K I≲J J≲K L I≲L J≲L I≲L≋I≲J≲L J≲L-uniq
  (K≲L , J≲L≋J≲K≲L , K≲L-uniq) = 
    ( pipe-≲ J K L J≲K J≲L K≲L J≲L≋J≲K≲L 
    , pipe-≋ I J K L I≲J I≲L J≲K J≲L K≲L I≲L≋I≲J≲L J≲L≋J≲K≲L
    , pipe-uniq I J K L I≲J I≲L J≲K J≲L K≲L J≲L≋J≲K≲L J≲L-uniq K≲L-uniq)

pipe-med′ : ∀ {V W X Y Z} → (I : Interp Σ X) → 
  (J : Interp Σ (X ⊕ V ⊕ Y)) → (K : Interp Σ (Y ⊕ W ⊕ Z)) →
    (I≲J : I ≲ inode * J) → (J≲K : enode * J ≲ inode * K) → 
      (L : Interp Σ (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z)) → (I≲L : I ≲ inode * L) → 
        (G : ABox Σ (Y ⊕ W ⊕ Z)) → (right * L ⊨ S , G) → 
          (Mediator (enode * J) K J≲K (S , G)) → 
            Mediated I J (left * L) I≲J I≲L →
              Mediated I (pipe J K J≲K) L (pipe-≳ I J K I≲J J≲K) I≲L
pipe-med′ I J K I≲J J≲K (L , l) I≲L G L⊨S,G K-med 
  (J≲L , I≲L≋I≲J≲L , J≲L-uniq) = 
    pipe-med″ I J K I≲J J≲K (L , l) I≲L J≲L I≲L≋I≲J≲L J≲L-uniq 
      (K-med (L , l ∘ right) (enode ** J≲L) L⊨S,G)

pipe-med : ∀ {V W X Y Z} → (I : Interp Σ X) → 
  (J : Interp Σ (X ⊕ V ⊕ Y)) → (K : Interp Σ (Y ⊕ W ⊕ Z)) →
    (I≲J : I ≲ inode * J) → (J≲K : enode * J ≲ inode * K) → 
      (F : ABox Σ (X ⊕ V ⊕ Y)) → (G : ABox Σ (Y ⊕ W ⊕ Z)) → 
        (Mediator I J I≲J (S , F)) → (Mediator (enode * J) K J≲K (S , G)) → 
          (Mediator I (pipe J K J≲K) (pipe-≳ I J K I≲J J≲K) (S , F ⟫ G))
pipe-med I J K I≲J J≲K F G J-med K-med 
  (L , l) I≲L (L⊨S , (L⊨F , L⊨G)) = 
    pipe-med′ I J K I≲J J≲K (L , l) I≲L G 
      (L⊨S , *-resp-⟨ABox⟩ right (L , l) G L⊨G) K-med
      (J-med (L , l ∘ left) I≲L (L⊨S , *-resp-⟨ABox⟩ left (L , l) F L⊨F))

pipe-ext″ : ∀ {V W X Y Z : Set} →
  (I : Interp Σ X) → (J : Interp Σ (X ⊕ V ⊕ Y)) → (I≲J : I ≲ inode * J) →
    (B : ABox Σ Y) → (C : ABox Σ Z) → 
      (F : ABox Σ (X ⊕ V ⊕ Y)) → (G : ABox Σ (Y ⊕ W ⊕ Z)) → 
        (J ⊨a F) → (Mediator I J I≲J (S , F)) →
          ((enode * J) ⊕ (S , G) ⊨ (T , C)) →
            (I ⊕ (S , F ⟫ G) ⊨ (T , C))
pipe-ext″ I (J , j) I≲J B C F G J⊨F J-med
  ((K , k) , ((J≲K , j≲k) , (K⊨S , K⊨G) , K-med) , (K⊨T , K⊨C)) = 
    ( pipe (J , j) (K , k) (J≲K , j≲k)
    , ( pipe-≳ I (J , j) (K , k) I≲J (J≲K , j≲k)
      , (K⊨S , pipe-⟫ (J , j) (K , k) (J≲K , j≲k) F G J⊨F K⊨G)
      , pipe-med I (J , j) (K , k) I≲J (J≲K , j≲k) F G J-med K-med )
    , (K⊨T , K⊨C) )

pipe-ext′ : ∀ {V X : Set}
  (I : Interp Σ X) → (B C : Object S T) → 
    (F : ABox Σ (X ⊕ V ⊕ IN B)) → (G : B ⇒ C) →
      (I ⊕  (S , F) ⊨ T , iface B) →
        (I ⊕ (S , F ⟫ impl G) ⊨ (T , iface C))
pipe-ext′ I (Y , Y∈Fin , B) (Z , Z∈Fin , C) F (W , G , G✓) 
  ((J , j) , (I≲J , (J⊨S , J⊨F) , J-med) , (J⊨T , J⊨B)) =
    pipe-ext″ I (J , j) I≲J B C F G J⊨F J-med
      (G✓ (J , j ∘ enode) ((J⊨S , J⊨T) , J⊨B))

pipe-ext : ∀ {A B C : Object S T} → (F : A ⇒ B) → (G : B ⇒ C) →
  ∀ I → (I ⊨ (S , T) , iface A) →
    (I ⊕ (S , impl F ⟫ impl G) ⊨ (T , iface C))
pipe-ext (V , F , F✓) G (I , i) ((I⊨S , I⊨T) , I⊨A) = 
  pipe-ext′ (I , i) _ _ F G (F✓ (I , i) ((I⊨S , I⊨T) , I⊨A))

compose : ∀ {A B C : Object S T} → (A ⇒ B) → (B ⇒ C) → (A ⇒ C)
compose {A} {B} F G = 
  ( (BN F ⊕ IN B ⊕ BN G)
  , (impl F ⟫ impl G)
  , (pipe-ext F G) )

