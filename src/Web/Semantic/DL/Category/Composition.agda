open import Data.Product using ( ∃ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox ; ⟨ABox⟩ ; _,_ )
open import Web.Semantic.DL.ABox.Interp using 
  ( Interp ; _,_ ; ⌊_⌋ ; ind ; _*_ )
open import Web.Semantic.DL.ABox.Interp.Morphism using 
  ( _≲_ ; _,_ ; _**_ ; ≲⌊_⌋ ; ≲-resp-ind ; _≋_ )
open import Web.Semantic.DL.ABox.Model using 
  ( _⊨a_ ; ⊨a-resp-≲ ; ⟨Abox⟩-resp-⊨ ; *-resp-⟨ABox⟩ 
  ; on-bnode ; bnodes ; _⊨b_ ; _,_ )
open import Web.Semantic.DL.Category.Morphism using 
  ( _⇒_ ; _,_ ; BN ; impl ; impl✓ )
open import Web.Semantic.DL.Category.Object using
  ( Object ; _,_ ; IN ; iface )
open import Web.Semantic.DL.Integrity using
  ( Unique ; Mediated ; Mediator ; Initial ; _⊕_⊨_ ; _>>_ ; _,_ 
  ; med-≲ ; med-≋ ; med-uniq ; init-≲ ; init-⊨ ; init-med
  ; extension ; ext-⊨ ; ext-init ; ext✓ )
open import Web.Semantic.DL.KB using ( KB ; _,_ )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox ; _,_ )
open import Web.Semantic.DL.TBox.Interp using 
  ( Δ ; _⊨_≈_ ; ≈-refl ; ≈-sym ; ≈-trans ) renaming
  ( Interp to Interp′ )
open import Web.Semantic.DL.TBox.Model using ( _⊨t_ )
open import Web.Semantic.DL.TBox.Interp.Morphism using 
  ( ≲-image ; ≲-refl ; ≲-trans ; ≲-resp-≈ ) renaming
  ( _≲_ to _≲′_ )
open import Web.Semantic.Util using 
  ( _⊕_⊕_ ; inode ; bnode ; enode ; left ; right ; merge ; _∘_ )

module Web.Semantic.DL.Category.Composition {Σ : Signature} where

infixr 5 _⟫_

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

pipe-left : ∀ {V W X Y Z} → (J : Interp Σ (X ⊕ V ⊕ Y)) → 
  (K : Interp Σ (Y ⊕ W ⊕ Z)) → (J≲K : enode * J ≲ inode * K) →
    (J ≲ left * (pipe J K J≲K))
pipe-left (J , j) (K , k) (J≲K , j≲k) = (J≲K , lemma) where

  lemma : ∀ x → 
    K ⊨ ≲-image J≲K (j x) ≈ merge (≲-image J≲K ∘ j) k (left x)
  lemma (inode x) = ≈-refl K
  lemma (bnode v) = ≈-refl K 
  lemma (enode y) = j≲k y

pipe-right : ∀ {V W X Y Z} → (J : Interp Σ (X ⊕ V ⊕ Y)) → 
  (K : Interp Σ (Y ⊕ W ⊕ Z)) → (J≲K : enode * J ≲ inode * K) →
    (K ≲ right * (pipe J K J≲K))
pipe-right (J , j) (K , k) (J≲K , j≲k) = (≲-refl K , lemma) where

  lemma : ∀ x → 
    K ⊨ k x ≈ merge (≲-image J≲K ∘ j) k (right x)
  lemma (inode y) = ≈-refl K
  lemma (bnode w) = ≈-refl K
  lemma (enode z) = ≈-refl K

pipe-exp :  ∀ {V W X Y Z} → (J : Interp Σ (X ⊕ V ⊕ Y)) → 
  (K : Interp Σ (Y ⊕ W ⊕ Z)) → (J≲K : enode * J ≲ inode * K) →
    ∀ KB → (enode * K ⊨ KB) → (enode * pipe J K J≲K ⊨ KB)
pipe-exp (J , j) (K , k) (J≲K , j≲k) KB K⊨KB = K⊨KB

⊨a-intro-⟫ : ∀ {V W X Y Z} → (I : Interp Σ (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z)) → 
  (F : ABox Σ (X ⊕ V ⊕ Y)) → (G : ABox Σ (Y ⊕ W ⊕ Z)) →
    (left * I ⊨a F) → (right * I ⊨a G) → (I ⊨a F ⟫ G)
⊨a-intro-⟫ (I , i) F G I⊨F I⊨G = 
  ( ⟨Abox⟩-resp-⊨ left (λ x → ≈-refl I) F I⊨F
  , ⟨Abox⟩-resp-⊨ right (λ x → ≈-refl I) G I⊨G )

⊨b-intro-⟫ : ∀ {V₁ W₁ V₂ W₂ X Y Z} → (I : Interp Σ (X ⊕ (V₁ ⊕ Y ⊕ W₁) ⊕ Z)) → 
  (F : ABox Σ (X ⊕ V₂ ⊕ Y)) → (G : ABox Σ (Y ⊕ W₂ ⊕ Z)) →
    (left * I ⊨b F) → (right * I ⊨b G) → (I ⊨b F ⟫ G)
⊨b-intro-⟫ {V₂ = V₂} {W₂ = W₂} {Y = Y} (I , i) F G (f , I⊨F) (g , I⊨G) = 
  (h , I⊨F⟫G) where

  h : (V₂ ⊕ Y ⊕ W₂) → Δ I
  h (inode v) = f v
  h (bnode y) = i (bnode (bnode y))
  h (enode w) = g w

  lemmaˡ : ∀ x → 
    I ⊨ on-bnode f (i ∘ left) x ≈ on-bnode h i (left x)
  lemmaˡ (inode x) = ≈-refl I
  lemmaˡ (bnode v) = ≈-refl I
  lemmaˡ (enode y) = ≈-refl I

  lemmaʳ : ∀ x → 
    I ⊨ on-bnode g (i ∘ right) x ≈ on-bnode h i (right x)
  lemmaʳ (inode x) = ≈-refl I
  lemmaʳ (bnode v) = ≈-refl I
  lemmaʳ (enode y) = ≈-refl I

  I⊨F⟫G : bnodes (I , i) h ⊨a F ⟫ G
  I⊨F⟫G = ⊨a-intro-⟫ (bnodes (I , i) h) F G 
    (⊨a-resp-≲ (≲-refl I , lemmaˡ) F I⊨F) 
    (⊨a-resp-≲ (≲-refl I , lemmaʳ) G I⊨G)

pipe-uniq : ∀ {V W X Y Z} I J K (M : Interp Σ (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z))
  (I≲J : I ≲ inode * J) (I≲M : I ≲ inode * M) →
    (J≲K : enode * J ≲ inode * K) (J≲M : J ≲ left * M) →
      (I≲M ≋ I≲J >> J≲M) →
        (Unique I J (left * M) I≲J I≲M) → 
          (Unique (enode * J) K (right * M) J≲K (enode ** J≲M)) → 
            (Unique I (pipe J K J≲K) M (pipe-≳ I J K I≲J J≲K) I≲M)
pipe-uniq {V} {W} {X} {Y} {Z} (I , i) (J , j) (K , k) (M , m)
  (I≲J , i≲j) (I≲M , i≲m) (J≲K , j≲k) (J≲M , j≲m) I≲M≋I≲J≲M J≲M-uniq K≲M-uniq 
    (L≲₁M , l≲₁m) (L≲₂M , l≲₂m) I≲M≋I≲L≲₁M I≲M≋I≲L≲₂M = 
      K≲M-uniq 
        (L≲₁M , lemmaʳ L≲₁M l≲₁m I≲M≋I≲L≲₁M) 
        (L≲₂M , lemmaʳ L≲₂M l≲₂m I≲M≋I≲L≲₂M) 
        (J≲M-uniq (J≲M , j≲m)
          (≲-trans J≲K L≲₁M , lemmaˡ L≲₁M l≲₁m I≲M≋I≲L≲₁M) 
          I≲M≋I≲J≲M 
          I≲M≋I≲L≲₁M ) 
        (J≲M-uniq (J≲M , j≲m)
          ( ≲-trans J≲K L≲₂M , lemmaˡ L≲₂M l≲₂m I≲M≋I≲L≲₂M)
          I≲M≋I≲J≲M 
          I≲M≋I≲L≲₂M ) where

  L : Interp′ Σ
  L = K

  l : (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z) → Δ L
  l = merge (≲-image J≲K ∘ j) k

  I≲L : I ≲′ L
  I≲L = ≲-trans I≲J J≲K

  lemmaˡ : ∀ L≲M → (∀ x → M ⊨ ≲-image L≲M (l x) ≈ m x) → 
    (∀ x → M ⊨ ≲-image I≲M x ≈ ≲-image L≲M (≲-image I≲L x)) → 
      ∀ x → M ⊨ ≲-image L≲M (≲-image J≲K (j x)) ≈ m (left x)
  lemmaˡ L≲M l≲m I≲M≋I≲L≲M (inode x) = l≲m (inode x)
  lemmaˡ L≲M l≲m I≲M≋I≲L≲M (bnode v) = l≲m (bnode (inode v))
  lemmaˡ L≲M l≲m I≲M≋I≲L≲M (enode y) = 
    ≈-trans M (≲-resp-≈ L≲M (j≲k y)) (l≲m (bnode (bnode y)))

  lemmaʳ : ∀ L≲M → (∀ x → M ⊨ ≲-image L≲M (l x) ≈ m x) → 
    (∀ x → M ⊨ ≲-image I≲M x ≈ ≲-image L≲M (≲-image I≲L x)) → 
      ∀ x → M ⊨ ≲-image L≲M (k x) ≈ m (right x)
  lemmaʳ L≲M l≲m I≲M≋I≲L≲M (inode y) = l≲m (bnode (bnode y))
  lemmaʳ L≲M l≲m I≲M≋I≲L≲M (bnode w) = l≲m (bnode (enode w))
  lemmaʳ L≲M l≲m I≲M≋I≲L≲M (enode z) = l≲m (enode z)

pipe-mediated : ∀ {V W X Y Z} I J K (M : Interp Σ (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z))
  (I≲J : I ≲ inode * J) (I≲M : I ≲ inode * M) →
    (J≲K : enode * J ≲ inode * K) →
      (m : Mediated I J (left * M) I≲J I≲M) → 
        (Mediated (enode * J) K (right * M) J≲K (enode ** (med-≲ m))) → 
          (Mediated I (pipe J K J≲K) M (pipe-≳ I J K I≲J J≲K) I≲M)
pipe-mediated {V} {W} {X} {Y} {Z} (I , i) (J , j) (K , k) (M , m)
  (I≲J , i≲j) (I≲M , i≲m) (J≲K , j≲k)
    ((J≲M , j≲m) , I≲M≋I≲J≲M , J≲M-uniq)
      ((K≲M , k≲m) , J≲M≋J≲K≲M , K≲M-uniq) = 
        ( (L≲M , l≲m) , I≲M≋I≲L≲M , L≲M-uniq) where 

  L : Interp′ Σ
  L = K

  l : (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z) → Δ L
  l = merge (≲-image J≲K ∘ j) k

  I≲L : I ≲′ L
  I≲L = ≲-trans I≲J J≲K

  i≲l : ∀ x → L ⊨ ≲-image I≲L (i x) ≈ l (inode x)
  i≲l x = ≲-resp-≈ J≲K (i≲j x)

  L≲M : L ≲′ M
  L≲M = K≲M

  l≲m : ∀ x → M ⊨ ≲-image K≲M (l x) ≈ m x
  l≲m (inode x) = 
    ≈-trans M (≈-sym M (J≲M≋J≲K≲M (j (inode x)))) (j≲m (inode x))
  l≲m (bnode (inode v)) =
    ≈-trans M (≈-sym M (J≲M≋J≲K≲M (j (bnode v)))) (j≲m (bnode v))
  l≲m (bnode (bnode y)) = k≲m (inode y)
  l≲m (bnode (enode w)) = k≲m (bnode w)
  l≲m (enode z) = k≲m (enode z)

  I≲M≋I≲L≲M : ∀ x → M ⊨ ≲-image I≲M x ≈ ≲-image L≲M (≲-image I≲L x)
  I≲M≋I≲L≲M x = ≈-trans M (I≲M≋I≲J≲M x) (J≲M≋J≲K≲M (≲-image I≲J x))
 
  L≲M-uniq : Unique (I , i) (L , l) (M , m) (I≲L , i≲l) (I≲M , i≲m)
  L≲M-uniq = pipe-uniq (I , i) (J , j) (K , k) (M , m)
    (I≲J , i≲j) (I≲M , i≲m) (J≲K , j≲k) (J≲M , j≲m)
      I≲M≋I≲J≲M J≲M-uniq K≲M-uniq

pipe-mediator : ∀ S {V W X Y Z I} 
  {J : Interp Σ (X ⊕ V ⊕ Y)} {K : Interp Σ (Y ⊕ W ⊕ Z)} {I≲J J≲K} F G →
    (Mediator I J I≲J (S , F)) → (Mediator (enode * J) K J≲K (S , G)) → 
      (Mediator I (pipe J K J≲K) (pipe-≳ I J K I≲J J≲K) (S , F ⟫ G))
pipe-mediator S {V} {W} {X} {Y} {Z} 
  {I , i} {J , j} {K , k} {I≲J , i≲j} {J≲K , j≲k}
    F G J-med K-med (M , m) (I≲M , i≲m) (M⊨S , M⊨F , M⊨G) =
      pipe-mediated (I , i) (J , j) (K , k) (M , m) 
        (I≲J , i≲j) (I≲M , i≲m) (J≲K , j≲k) 
          I≲J≲M-med J≲K≲M-med where

  mˡ : (X ⊕ V ⊕ Y) → Δ M
  mˡ x = m (left x) 

  mʳ : (Y ⊕ W ⊕ Z) → Δ M
  mʳ x = m (right x) 

  I≲J≲M-med : Mediated (I , i) (J , j) (M , mˡ) (I≲J , i≲j) (I≲M , i≲m)
  I≲J≲M-med = J-med (M , mˡ) (I≲M , i≲m) 
    (M⊨S , *-resp-⟨ABox⟩ left (M , m) F M⊨F)

  J≲M : J ≲′ M
  J≲M = ≲⌊ med-≲ I≲J≲M-med ⌋

  j≲m : ∀ x → M ⊨ ≲-image J≲M (j x) ≈ mˡ x
  j≲m = ≲-resp-ind (med-≲ I≲J≲M-med)

  j′ : Y → Δ J
  j′ y = j (enode y)

  j≲m′ : ∀ x → M ⊨ ≲-image J≲M (j′ x) ≈ m (bnode (bnode x))
  j≲m′ x = j≲m (enode x)

  J≲K≲M-med : Mediated (J , j′) (K , k) (M , mʳ) (J≲K , j≲k) (J≲M , j≲m′)
  J≲K≲M-med = K-med (M , mʳ) (J≲M , j≲m′) 
    (M⊨S , *-resp-⟨ABox⟩ right (M , m) G M⊨G)

pipe-init : ∀ {S V W X Y Z I} 
  {J : Interp Σ (X ⊕ V ⊕ Y)} {K : Interp Σ (Y ⊕ W ⊕ Z)} {F G} →
    (J-init : J ∈ Initial I (S , F)) →
      (K-init : K ∈ Initial (enode * J) (S , G)) →
        (pipe J K (init-≲ K-init) ∈ Initial I (S , F ⟫ G))
pipe-init {S} {V} {W} {X} {Y} {Z} {I , i} {J , j} {K , k} {F} {G}
  ((I≲J , i≲j) , (J⊨S , J⊨F) , J-med) ((J≲K , j≲k) , (K⊨S , K⊨G) , K-med) =
    ( (I≲L , i≲l) , (L⊨S , L⊨F⟫G) , L-med) where

  L : Interp′ Σ
  L = K

  l : (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z) → Δ L
  l = merge (≲-image J≲K ∘ j) k

  I≲L : I ≲′ L
  I≲L = ≲-trans I≲J J≲K

  i≲l : ∀ x → L ⊨ ≲-image I≲L (i x) ≈ l (inode x)
  i≲l x = ≲-resp-≈ J≲K (i≲j x)

  L⊨S : L ⊨t S
  L⊨S = K⊨S

  L⊨F⟫G : (L , l) ⊨a F ⟫ G
  L⊨F⟫G = ⊨a-intro-⟫ (L , l) F G 
    (⊨a-resp-≲ (pipe-left (J , j) (K , k) (J≲K , j≲k)) F J⊨F) 
    (⊨a-resp-≲ (pipe-right (J , j) (K , k) (J≲K , j≲k)) G K⊨G)

  L-med : Mediator (I , i) (L , l) (I≲L , i≲l) (S , F ⟫ G)
  L-med = pipe-mediator S F G J-med K-med

compose-⊨ : ∀ {S T V W X Y Z} A B C 
  (F : ABox Σ (X ⊕ V ⊕ Y)) (G : ABox Σ (Y ⊕ W ⊕ Z)) →
    (∀ I → (I ⊨ (S , T) , A) → (I ⊕ S , F ⊨ T , B)) →
      (∀ J → (J ⊨ (S , T) , B) → (J ⊕ S , G ⊨ T , C)) →
        (∀ I → (I ⊨ (S , T) , A) → (I ⊕ S , F ⟫ G ⊨ T , C))
compose-⊨ {S} {T} {V} {W} {X} {Y} {Z} A B C F G F✓ G✓ (I , i) I⊨STA = 
  ( pipe J K J≲K
  , pipe-init J-init K-init
  , pipe-exp J K J≲K (T , C) K⊨TC ) where

  I⊕SF⊨TB : I , i ⊕ S , F ⊨ T , B
  I⊕SF⊨TB = F✓ (I , i) I⊨STA
  
  J : Interp Σ (X ⊕ V ⊕ Y)
  J = extension I⊕SF⊨TB

  J-init : J ∈ Initial (I , i) (S , F)
  J-init = ext-init I⊕SF⊨TB

  J⊕SG⊨TC : enode * J ⊕ S , G ⊨ T , C
  J⊕SG⊨TC = G✓ (enode * J) (ext✓ I⊕SF⊨TB)

  K : Interp Σ (Y ⊕ W ⊕ Z)
  K = extension J⊕SG⊨TC

  K⊨TC : enode * K ⊨ (T , C)
  K⊨TC = ext-⊨ J⊕SG⊨TC

  K-init : K ∈ Initial (enode * J) (S , G)
  K-init = ext-init J⊕SG⊨TC

  J≲K : enode * J ≲ inode * K
  J≲K = init-≲ K-init

compose : ∀ {S T} {A B C : Object S T} → (A ⇒ B) → (B ⇒ C) → (A ⇒ C)
compose {S} {T} {A} {B} {C} F G = 
  ( BN F ⊕ IN B ⊕ BN G
  , impl F ⟫ impl G 
  , compose-⊨ (iface A) (iface B) (iface C) (impl F) (impl G) (impl✓ F) (impl✓ G) )
