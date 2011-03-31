open import Data.Product using ( ∃ ; _×_ ; _,_ )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox )
open import Web.Semantic.DL.ABox.Interp using ( Interp ; _*_ )
open import Web.Semantic.DL.KB using ( _,_ )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.KB.Initial using ( _⊕_⊨_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox ; _,_ )
open import Web.Semantic.DL.Category.Object using ( Object ; _,_ ; IN ; iface )
open import Web.Semantic.Util using ( _⊕_⊕_ ; inode ; enode )

module Web.Semantic.DL.Category.Morphism {Σ : Signature} {S T : TBox Σ} where

infixr 5 _,_

-- A morphism A ⇒ B is an abox F such that for every I ⊨ S , T , A
-- there is a J which is the initial extension of I satisfying (S , F),
-- and moreover J satisfies (T , B).

data _⇒_ (A B : Object S T) : Set₁ where
  _,_ : ∀ V → (∃ λ (F : ABox Σ (IN A ⊕ V ⊕ IN B)) →
      ∀ I → (I ⊨ (S , T) , iface A) → (I ⊕ (S , F) ⊨ (T , iface B))) →
    (A ⇒ B)

BN : ∀ {A B} → (F : A ⇒ B) → Set
BN (V , F , F✓) = V

impl : ∀ {A B} → (F : A ⇒ B) → ABox Σ (IN A ⊕ BN F ⊕ IN B)
impl (V , F , F✓) = F
