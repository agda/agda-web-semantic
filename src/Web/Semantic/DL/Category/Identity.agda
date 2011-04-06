open import Data.List using ( List ; [] ; _∷_ )
open import Data.List.Any using ( here ; there )
open import Data.Product using ( ∃ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox ; ε ; _,_ ; _∼_ )
open import Web.Semantic.DL.ABox.Interp using
  ( Interp ; _,_ ; ind ; _*_ ; ⌊_⌋ )
open import Web.Semantic.DL.ABox.Interp.Morphism using
  ( _≲_ ; _≋_ ; _,_ ; ≲⌊_⌋ ; ≲-resp-ind )
open import Web.Semantic.DL.ABox.Model using ( _⊨a_ ; ⊨a-resp-≲ )
open import Web.Semantic.DL.Integrity using 
  ( _>>_ ; Unique ; Mediator ; Initial ; _⊕_⊨_ ; _,_ )
open import Web.Semantic.DL.KB using ( _,_ )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox ; _,_ )
open import Web.Semantic.DL.TBox.Interp using 
  ( Δ ; _⊨_≈_ ; con ; rol ; con-≈ ; rol-≈ ; ≈-refl ; ≈-sym ; ≈-trans )
open import Web.Semantic.DL.TBox.Interp.Morphism using
  ( ≲-image ; ≲-resp-≈ ; ≲-resp-con ; ≲-resp-rol ; ≲-refl )
open import Web.Semantic.DL.Category.Object using ( Object ; _,_ ; IN ; fin ; iface )
open import Web.Semantic.DL.Category.Morphism using ( _⇒_ ; _,_ ; impl )
open import Web.Semantic.Util using
  ( False ; Finite ; elim ; _∈ˡ_ ; _⊕_⊕_ 
  ; id ; _∘_ ; tt ; _[⊕]_[⊕]_ ; inode ; bnode ; enode )

module Web.Semantic.DL.Category.Identity {Σ : Signature} {S T : TBox Σ} where

wire : ∀ {X} → List X → ABox Σ (X ⊕ False ⊕ X)
wire [] = ε
wire (x ∷ xs) = (inode x ∼ enode x , wire xs)

wire-≈ : ∀ {X I xs} {x : X} → (x ∈ˡ xs) → (I ⊨a wire xs) →
  (⌊ I ⌋ ⊨ ind I (inode x) ≈ ind I (enode x))
wire-≈ (here refl)  (x₁≈x₂ , xs₁≈xs₂) = x₁≈x₂
wire-≈ (there x∈xs) (x₁≈x₂ , xs₁≈xs₂) = wire-≈ x∈xs xs₁≈xs₂

wire-≈⁻¹ : ∀ {X I} → (∀ x → (⌊ I ⌋ ⊨ ind I (inode x) ≈ ind I (enode x))) → 
  ∀ (xs : List X) → (I ⊨a wire xs)
wire-≈⁻¹ ∀x∙x₁≈x₂ []       = tt
wire-≈⁻¹ ∀x∙x₁≈x₂ (x ∷ xs) = (∀x∙x₁≈x₂ x , wire-≈⁻¹ ∀x∙x₁≈x₂ xs)

identity : ∀ (A : Object S T) → (A ⇒ A)
identity A = (False , F , F✓) where

  xs : List (IN A)
  xs = proj₁ (fin A)

  ∀x∙x∈xs : ∀ x → x ∈ˡ xs
  ∀x∙x∈xs = proj₂ (fin A)

  F : ABox Σ (IN A ⊕ False ⊕ IN A)
  F = wire xs

  F✓ : ∀ I → (I ⊨ (S , T) , iface A) → (I ⊕ (S , F) ⊨ (T , iface A))
  F✓ I ((I⊨S , I⊨T) , I⊨A) = 
    (J , (I≲J , (I⊨S , J⊨F) , init) , (I⊨T , J⊨A)) where

    j : IN A ⊕ False ⊕ IN A → Δ ⌊ I ⌋
    j = ind I [⊕] elim [⊕] ind I

    J : Interp Σ (IN A ⊕ False ⊕ IN A)
    J = (⌊ I ⌋ , j)

    i≲j : ∀ x → (⌊ J ⌋ ⊨ ind I x ≈ ind J (inode x))
    i≲j x = ≈-refl ⌊ J ⌋

    I≲J : I ≲ inode * J
    I≲J = (≲-refl ⌊ I ⌋ , i≲j)

    J⊨F : J ⊨a F
    J⊨F = wire-≈⁻¹ (λ x → ≈-refl ⌊ I ⌋) xs

    J⊨A : enode * J ⊨a iface A
    J⊨A = ⊨a-resp-≲ I≲J (iface A) I⊨A

    init : Mediator I J I≲J (S , F)
    init K I≲K (K⊨S , K⊨F) = 
      (J≲K , I≲K≋I≲J≲K , uniq) where

      j≲k : ∀ x → ⌊ K ⌋ ⊨ ≲-image ≲⌊ I≲K ⌋ (ind J x) ≈ ind K x
      j≲k (inode x) = ≲-resp-ind I≲K x
      j≲k (bnode ())
      j≲k (enode x) = ≈-trans ⌊ K ⌋ (≲-resp-ind I≲K x) (wire-≈ (∀x∙x∈xs x) K⊨F)

      J≲K : J ≲ K
      J≲K = (≲⌊ I≲K ⌋ , j≲k)

      I≲K≋I≲J≲K : I≲K ≋ I≲J >> J≲K
      I≲K≋I≲J≲K x = ≈-refl ⌊ K ⌋

      uniq : Unique I J K I≲J I≲K
      uniq J≲₁K J≲₂K I≲K≋I≲J≲₁K I≲K≋I≲J≲₂K x =
         ≈-trans ⌊ K ⌋ (≈-sym ⌊ K ⌋ (I≲K≋I≲J≲₁K x)) (I≲K≋I≲J≲₂K x)
