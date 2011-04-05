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
  ( Δ ; _⊨_≈_ ; ≈-refl ; ≈-sym ; ≈-trans )
open import Web.Semantic.DL.TBox.Model using ( _⊨t_ )
open import Web.Semantic.DL.TBox.Interp.Morphism using 
  ( ≲-image ; ≲-refl ; ≲-trans ; ≲-resp-≈ )
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
pipe J K J≲K = (⌊ K ⌋ , merge (≲-image ≲⌊ J≲K ⌋ ∘ ind J) (ind K))

pipe-≳ : ∀ {V W X Y Z} → (I : Interp Σ X) → 
  (J : Interp Σ (X ⊕ V ⊕ Y)) → (K : Interp Σ (Y ⊕ W ⊕ Z)) →
    (I≲J : I ≲ inode * J) → (J≲K : enode * J ≲ inode * K) → 
      (I ≲ inode * (pipe J K J≲K))
pipe-≳ I J K I≲J J≲K = 
  (≲-trans ≲⌊ I≲J ⌋ ≲⌊ J≲K ⌋ , λ x → ≲-resp-≈ ≲⌊ J≲K ⌋ (≲-resp-ind I≲J x))

pipe-left : ∀ {V W X Y Z} → (J : Interp Σ (X ⊕ V ⊕ Y)) → 
  (K : Interp Σ (Y ⊕ W ⊕ Z)) → (J≲K : enode * J ≲ inode * K) →
    (J ≲ left * (pipe J K J≲K))
pipe-left J K J≲K = (≲⌊ J≲K ⌋ , lemma) where

  lemma : ∀ x → 
    ⌊ K ⌋ ⊨ ≲-image ≲⌊ J≲K ⌋ (ind J x) ≈ ind (left * pipe J K J≲K) x
  lemma (inode x) = ≈-refl ⌊ K ⌋
  lemma (bnode v) = ≈-refl ⌊ K ⌋
  lemma (enode y) = ≲-resp-ind J≲K y

pipe-right : ∀ {V W X Y Z} → (J : Interp Σ (X ⊕ V ⊕ Y)) → 
  (K : Interp Σ (Y ⊕ W ⊕ Z)) → (J≲K : enode * J ≲ inode * K) →
    (K ≲ right * (pipe J K J≲K))
pipe-right J K J≲K = (≲-refl ⌊ K ⌋ , lemma) where

  lemma : ∀ x → 
    ⌊ K ⌋ ⊨ ind K x ≈ ind (right * pipe J K J≲K) x
  lemma (inode y) = ≈-refl ⌊ K ⌋
  lemma (bnode w) = ≈-refl ⌊ K ⌋
  lemma (enode z) = ≈-refl ⌊ K ⌋

⊨a-intro-⟫ : ∀ {V W X Y Z} → (I : Interp Σ (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z)) → 
  (F : ABox Σ (X ⊕ V ⊕ Y)) → (G : ABox Σ (Y ⊕ W ⊕ Z)) →
    (left * I ⊨a F) → (right * I ⊨a G) → (I ⊨a F ⟫ G)
⊨a-intro-⟫ (I , i) F G I⊨F I⊨G = 
  ( ⟨Abox⟩-resp-⊨ left (λ x → ≈-refl I) F I⊨F
  , ⟨Abox⟩-resp-⊨ right (λ x → ≈-refl I) G I⊨G)

⊨b-intro-⟫ : ∀ {V₁ W₁ V₂ W₂ X Y Z} → (I : Interp Σ (X ⊕ (V₁ ⊕ Y ⊕ W₁) ⊕ Z)) → 
  (F : ABox Σ (X ⊕ V₂ ⊕ Y)) → (G : ABox Σ (Y ⊕ W₂ ⊕ Z)) →
    (left * I ⊨b F) → (right * I ⊨b G) → (I ⊨b F ⟫ G)
⊨b-intro-⟫ {V₂ = V₂} {W₂ = W₂} {Y = Y} I F G (f , I⊨F) (g , I⊨G) = 
  (h , I⊨F⟫G) where

  h : (V₂ ⊕ Y ⊕ W₂) → Δ ⌊ I ⌋
  h (inode v) = f v
  h (bnode y) = ind I (bnode (bnode y))
  h (enode w) = g w

  lemmaˡ : ∀ x → 
    ⌊ I ⌋ ⊨ on-bnode f (ind I ∘ left) x ≈ on-bnode h (ind I) (left x)
  lemmaˡ (inode x) = ≈-refl ⌊ I ⌋
  lemmaˡ (bnode v) = ≈-refl ⌊ I ⌋
  lemmaˡ (enode y) = ≈-refl ⌊ I ⌋

  lemmaʳ : ∀ x → 
    ⌊ I ⌋ ⊨ on-bnode g (ind I ∘ right) x ≈ on-bnode h (ind I) (right x)
  lemmaʳ (inode x) = ≈-refl ⌊ I ⌋
  lemmaʳ (bnode v) = ≈-refl ⌊ I ⌋
  lemmaʳ (enode y) = ≈-refl ⌊ I ⌋

  I⊨F⟫G : bnodes I h ⊨a F ⟫ G
  I⊨F⟫G = ⊨a-intro-⟫ (bnodes I h) F G 
    (⊨a-resp-≲ (≲-refl ⌊ I ⌋ , lemmaˡ) F I⊨F) 
    (⊨a-resp-≲ (≲-refl ⌊ I ⌋ , lemmaʳ) G I⊨G)

pipe-uniq : ∀ {V W X Y Z I J K} {M : Interp Σ (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z)} 
  (I≲J : I ≲ inode * J) (I≲M : I ≲ inode * M) →
    (J≲K : enode * J ≲ inode * K) (J≲M : J ≲ left * M) →
      (I≲M ≋ I≲J >> J≲M) →
        (Unique I J (left * M) I≲J I≲M) → 
          (Unique (enode * J) K (right * M) J≲K (enode ** J≲M)) → 
            (Unique I (pipe J K J≲K) M (pipe-≳ I J K I≲J J≲K) I≲M)
pipe-uniq {I = I} {J = J} {K = K} {M = M}
  I≲J I≲M J≲K J≲M I≲M≋I≲J≲M J≲M-uniq K≲M-uniq 
    L≲₁M L≲₂M I≲M≋I≲L≲₁M I≲M≋I≲L≲₂M = 
      K≲M-uniq 
        (≲⌊ L≲₁M ⌋ , lemmaʳ L≲₁M I≲M≋I≲L≲₁M) 
        (≲⌊ L≲₂M ⌋ , lemmaʳ L≲₂M I≲M≋I≲L≲₂M) 
        (J≲M-uniq J≲M 
          ( ≲-trans ≲⌊ J≲K ⌋ ≲⌊ L≲₁M ⌋ , lemmaˡ L≲₁M I≲M≋I≲L≲₁M) 
          I≲M≋I≲J≲M 
          I≲M≋I≲L≲₁M ) 
        (J≲M-uniq J≲M 
          ( ≲-trans ≲⌊ J≲K ⌋ ≲⌊ L≲₂M ⌋ , lemmaˡ L≲₂M I≲M≋I≲L≲₂M)
          I≲M≋I≲J≲M 
          I≲M≋I≲L≲₂M ) where

  L = pipe J K J≲K
  I≲L = pipe-≳ I J K I≲J J≲K

  lemmaˡ : ∀ L≲M → (I≲M ≋ I≲L >> L≲M) → ∀ x → 
    ⌊ M ⌋ ⊨ ≲-image ≲⌊ L≲M ⌋ (≲-image ≲⌊ J≲K ⌋ (ind J x)) ≈ ind M (left x)
  lemmaˡ L≲M I≲M≋I≲L≲M (inode x) = ≲-resp-ind L≲M (inode x)
  lemmaˡ L≲M I≲M≋I≲L≲M (bnode v) = ≲-resp-ind L≲M (bnode (inode v))
  lemmaˡ L≲M I≲M≋I≲L≲M (enode y) = ≈-trans ⌊ M ⌋ 
    (≲-resp-≈ ≲⌊ L≲M ⌋ (≲-resp-ind J≲K y)) 
    (≲-resp-ind L≲M (bnode (bnode y)))

  lemmaʳ : ∀ L≲M → (I≲M ≋ I≲L >> L≲M) → ∀ x → 
    ⌊ M ⌋ ⊨ ≲-image ≲⌊ L≲M ⌋ (ind K x) ≈ ind M (right x)
  lemmaʳ L≲M I≲M≋I≲L≲M (inode y) = ≲-resp-ind L≲M (bnode (bnode y))
  lemmaʳ L≲M I≲M≋I≲L≲M (bnode w) = ≲-resp-ind L≲M (bnode (enode w))
  lemmaʳ L≲M I≲M≋I≲L≲M (enode z) = ≲-resp-ind L≲M (enode z)

pipe-med : ∀ S {V W X Y Z I} 
  {J : Interp Σ (X ⊕ V ⊕ Y)} {K : Interp Σ (Y ⊕ W ⊕ Z)} F G {I≲J J≲K} →
    (Mediator I J I≲J (S , F)) → (Mediator (enode * J) K J≲K (S , G)) → 
      (Mediator I (pipe J K J≲K) (pipe-≳ I J K I≲J J≲K) (S , F ⟫ G))
pipe-med S {V} {W} {X} {Y} {Z} {I} {J} {K} F G {I≲J} {J≲K}
   J-med K-med M I≲M (M⊨S , M⊨F , M⊨G) = 
    (L≲M , I≲M≋I≲L≲M , L≲M-uniq) where

  L : Interp Σ (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z)
  L = pipe J K J≲K

  I≲L : I ≲ inode * L
  I≲L = pipe-≳ I J K I≲J J≲K

  I≲J≲M-med : Mediated I J (left * M) I≲J I≲M
  I≲J≲M-med = J-med (left * M) I≲M (M⊨S , *-resp-⟨ABox⟩ left M F M⊨F)

  J≲M : J ≲ left * M
  J≲M = med-≲ I≲J≲M-med

  I≲M≋I≲J≲M : I≲M ≋ I≲J >> J≲M
  I≲M≋I≲J≲M = med-≋ I≲J≲M-med

  J≲M-uniq : Unique I J (left * M) I≲J I≲M
  J≲M-uniq = med-uniq I≲J≲M-med

  J≲K≲M-med : Mediated (enode * J) K (right * M) J≲K (enode ** J≲M)
  J≲K≲M-med = K-med (right * M) (enode ** J≲M) 
    (M⊨S , *-resp-⟨ABox⟩ right M G M⊨G)

  K≲M : K ≲ right * M
  K≲M = med-≲ J≲K≲M-med

  J≲M≋J≲K≲M : enode ** J≲M ≋ J≲K >> K≲M
  J≲M≋J≲K≲M = med-≋ J≲K≲M-med

  K≲M-uniq : Unique (enode * J) K (right * M) J≲K (enode ** J≲M)
  K≲M-uniq = med-uniq J≲K≲M-med

  lemma : ∀ x → ⌊ M ⌋ ⊨ ≲-image ≲⌊ K≲M ⌋ (ind L x) ≈ ind M x
  lemma (inode x) = ≈-trans ⌊ M ⌋ 
    (≈-sym ⌊ M ⌋ (J≲M≋J≲K≲M (ind J (inode x)))) 
    (≲-resp-ind J≲M (inode x))
  lemma (bnode (inode v)) = ≈-trans ⌊ M ⌋ 
    (≈-sym ⌊ M ⌋ (J≲M≋J≲K≲M (ind J (bnode v)))) 
    (≲-resp-ind J≲M (bnode v))
  lemma (bnode (bnode y)) = ≲-resp-ind K≲M (inode y)
  lemma (bnode (enode w)) = ≲-resp-ind K≲M (bnode w)
  lemma (enode z) = ≲-resp-ind K≲M (enode z)

  L≲M : L ≲ M
  L≲M = (≲⌊ K≲M ⌋ , lemma)

  I≲M≋I≲L≲M : I≲M ≋ I≲L >> L≲M
  I≲M≋I≲L≲M x = ≈-trans ⌊ M ⌋ (I≲M≋I≲J≲M x) (J≲M≋J≲K≲M (≲-image ≲⌊ I≲J ⌋ x))
 
  L≲M-uniq : Unique I L M I≲L I≲M
  L≲M-uniq = pipe-uniq I≲J I≲M J≲K J≲M I≲M≋I≲J≲M J≲M-uniq K≲M-uniq

pipe-init : ∀ {S V W X Y Z I} 
  {J : Interp Σ (X ⊕ V ⊕ Y)} {K : Interp Σ (Y ⊕ W ⊕ Z)} {F G} →
    (J-init : J ∈ Initial I (S , F)) →
      (K-init : K ∈ Initial (enode * J) (S , G)) →
        (pipe J K (init-≲ K-init) ∈ Initial I (S , F ⟫ G))
pipe-init {S} {V} {W} {X} {Y} {Z} {I} {J} {K} {F} {G} J-init K-init = 
  ( I≲L , (L⊨S , L⊨F⟫G) , L-med) where

   I≲J : I ≲ inode * J
   I≲J = init-≲ J-init

   J≲K : enode * J ≲ inode * K
   J≲K = init-≲ K-init

   L : Interp Σ (X ⊕ (V ⊕ Y ⊕ W) ⊕ Z)
   L = pipe J K J≲K

   I≲L : I ≲ inode * L
   I≲L = pipe-≳ I J K I≲J J≲K

   L⊨S : ⌊ L ⌋ ⊨t S
   L⊨S = proj₁ (init-⊨ K-init)

   J⊨F : J ⊨a F
   J⊨F = proj₂ (init-⊨ J-init)

   K⊨G : K ⊨a G
   K⊨G = proj₂ (init-⊨ K-init)

   L⊨F⟫G : L ⊨a F ⟫ G
   L⊨F⟫G = ⊨a-intro-⟫ L F G 
     (⊨a-resp-≲ (pipe-left J K J≲K) F J⊨F) 
     (⊨a-resp-≲ (pipe-right J K J≲K) G K⊨G)

   L-med : Mediator I L I≲L (S , F ⟫ G)
   L-med = pipe-med S F G (init-med J-init) (init-med K-init)

compose-⊨ : ∀ {S T V W X Y Z} A B C 
  (F : ABox Σ (X ⊕ V ⊕ Y)) (G : ABox Σ (Y ⊕ W ⊕ Z)) →
    (∀ I → (I ⊨ (S , T) , A) → (I ⊕ S , F ⊨ T , B)) →
      (∀ J → (J ⊨ (S , T) , B) → (J ⊕ S , G ⊨ T , C)) →
        (∀ I → (I ⊨ (S , T) , A) → (I ⊕ S , F ⟫ G ⊨ T , C))
compose-⊨ {S} {T} {V} {W} {X} {Y} {Z} A B C F G F✓ G✓ I I⊨STA = 
  (pipe J K J≲K , pipe-init J-init K-init , K⊨TC) where

  I⊕SF⊨TB : I ⊕ S , F ⊨ T , B
  I⊕SF⊨TB = F✓ I I⊨STA
  
  J : Interp Σ (X ⊕ V ⊕ Y)
  J = extension I⊕SF⊨TB

  J-init : J ∈ Initial I (S , F)
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
