open import Data.Product using ( ∃ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox )
open import Web.Semantic.DL.ABox.Model using ( _⊨a_ ; _⊨b_ ; ⊨a-resp-≲ ; ⊨b-resp-≲ )
open import Web.Semantic.DL.ABox.Interp using ( Interp ; ⌊_⌋ ; _*_ )
open import Web.Semantic.DL.ABox.Interp.Morphism using ( _≲_ ; ≲-refl )
open import Web.Semantic.DL.KB using ( _,_ )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.Integrity using ( Initial ; _⊕_⊨_ ; extension ; ext-init ; ext-⊨ ; ext✓ ; init-≲ ; init-⊨ ; init-med ; med-≲ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox ; _,_ )
open import Web.Semantic.DL.TBox.Model using ( _⊨t_ )
open import Web.Semantic.DL.Category.Object using ( Object ; _,_ ; IN ; iface )
open import Web.Semantic.Util using ( _⊕_⊕_ ; inode ; enode )

module Web.Semantic.DL.Category.Morphism {Σ : Signature} {S T : TBox Σ} where

infixr 4 _,_

-- A morphism A ⇒ B is an abox F such that for every I ⊨ S , T , A
-- there is a J which is the initial extension of I satisfying (S , F),
-- and moreover J satisfies (T , B).

data _⇒_w/_ (A B : Object S T) (V : Set) : Set₁ where
  _,_ : (F : ABox Σ (IN A ⊕ V ⊕ IN B)) →
    (∀ I → (I ⊨ (S , T) , iface A) → (I ⊕ (S , F) ⊨ (T , iface B))) →
      (A ⇒ B w/ V)

data _⇒_ (A B : Object S T) : Set₁ where
  _,_ : ∀ V → (A ⇒ B w/ V) → (A ⇒ B)

BN : ∀ {A B} → (F : A ⇒ B) → Set
BN (V , F,F✓) = V

impl : ∀ {A B} → (F : A ⇒ B) → ABox Σ (IN A ⊕ BN F ⊕ IN B)
impl (V , F , F✓) = F

impl✓ : ∀ {A B} → (F : A ⇒ B) → ∀ I → (I ⊨ (S , T) , iface A) → (I ⊕ (S , impl F) ⊨ (T , iface B))
impl✓ (V , F , F✓) = F✓

apply : ∀ {A B} (F : A ⇒ B) I → (I ⊨ (S , T) , iface A) → 
  Interp Σ (IN A ⊕ BN F ⊕ IN B)
apply F I I⊨STA = extension (impl✓ F I I⊨STA)

apply-init : ∀ {A B} (F : A ⇒ B) I I⊨STA →
  (apply F I I⊨STA ∈ Initial I (S , impl F))
apply-init F I I⊨STA = ext-init (impl✓ F I I⊨STA)

apply-⊨ : ∀ {A B} (F : A ⇒ B) I I⊨STA →
  (enode * (apply F I I⊨STA) ⊨ (T , iface B))
apply-⊨ F I I⊨STA = ext-⊨ (impl✓ F I I⊨STA)

apply-≲ : ∀ {A B} (F : A ⇒ B) I I⊨STA → (I ⊨a impl F) →
  (apply F (inode * I) I⊨STA ≲ I)
apply-≲ F I ((I⊨S , I⊨T) , I⊨A) I⊨F = 
  med-≲ (init-med 
    (apply-init F (inode * I) ((I⊨S , I⊨T) , I⊨A)) 
    I 
    (≲-refl (inode * I)) 
    (I⊨S , I⊨F))

apply✓ : ∀ {A B} (F : A ⇒ B) I I⊨STA →
  (enode * apply F I I⊨STA ⊨ (S , T) , iface B)
apply✓ F I I⊨STA = ext✓ (impl✓ F I I⊨STA)

-- Morphisms F and G are equivalent whenever
-- in any interpretation I ⊨ S,T
-- we have I ⊨ F iff I ⊨ G.

infix 2 _⊑_ _⊑′_ _≣_

_⊑_ : ∀ {A B : Object S T} → (A ⇒ B) → (A ⇒ B) → Set₁
_⊑_ {A} F G = 
  ∀ I → (inode * I ⊨ (S , T) , iface A) → (I ⊨a impl F) → (I ⊨b impl G)

data _≣_ {A B : Object S T} (F G : A ⇒ B) : Set₁ where
  _,_ : (F ⊑ G) → (G ⊑ F) → (F ≣ G)

-- An alternative characterization, which may be easier
-- to work with.

_⊑′_ : ∀ {A B : Object S T} → (A ⇒ B) → (A ⇒ B) → Set₁
F ⊑′ G = ∀ I I⊨STA → (apply F I I⊨STA) ⊨b (impl G)
  
⊑′-impl-⊑ : ∀ {A B : Object S T} → (F G : A ⇒ B) → (F ⊑′ G) → (F ⊑ G)
⊑′-impl-⊑ F G F⊑′G I I⊨STA I⊨F = 
  ⊨b-resp-≲ (apply-≲ F I I⊨STA I⊨F) (impl G) (F⊑′G (inode * I) I⊨STA)

⊑-impl-⊑′ : ∀ {A B : Object S T} → (F G : A ⇒ B) → (F ⊑ G) → (F ⊑′ G)
⊑-impl-⊑′ {A} {B} F G F⊑G I (I⊨ST , I⊨A) = J⊨G where

  J : Interp Σ (IN A ⊕ BN F ⊕ IN B)
  J = apply F I (I⊨ST , I⊨A)

  J⊨S : ⌊ J ⌋ ⊨t S
  J⊨S = proj₁ (init-⊨ (apply-init F I (I⊨ST , I⊨A)))

  J⊨T : ⌊ J ⌋ ⊨t T
  J⊨T = proj₁ (apply-⊨ F I (I⊨ST , I⊨A))

  J⊨A : inode * J ⊨a iface A
  J⊨A = ⊨a-resp-≲ (init-≲ (apply-init F I (I⊨ST , I⊨A))) (iface A) I⊨A

  J⊨F : J ⊨a impl F
  J⊨F = proj₂ (init-⊨ (apply-init F I (I⊨ST , I⊨A)))

  J⊨G : J ⊨b impl G
  J⊨G = F⊑G J ((J⊨S , J⊨T) , J⊨A) J⊨F

