open import Data.List using ( List ; [] ; _∷_ )
open import Data.List.Any using ( here ; there )
open import Data.Product using ( ∃ ; _×_ ; _,_ )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Relation.Unary using ( _∈_ )
open import Web.Semantic.DL.ABox using ( ABox ; ε ; _,_ ; _∼_ )
open import Web.Semantic.DL.ABox.Interp using ( Interp ; _,_ ; ind ; _*_ ; ⌊_⌋ )
open import Web.Semantic.DL.ABox.Interp.Morphism using ( _≲_ ; _≋_ ; _,_ )
open import Web.Semantic.DL.ABox.Model using ( _⊨a_ )
open import Web.Semantic.DL.Integrity using ( _>>_ ; Mediator ; Initial ; _⊕_⊨_ ; _,_ )
open import Web.Semantic.DL.KB using ( _,_ )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox ; _,_ )
open import Web.Semantic.DL.TBox.Interp using ( Δ ; _⊨_≈_ ; con ; rol ; con-≈ ; rol-≈ ; ≈-refl ; ≈-trans )
open import Web.Semantic.DL.TBox.Interp.Morphism using ( ≲-image ; ≲-resp-≈ ; ≲-resp-con ; ≲-resp-rol ; ≲-refl )
open import Web.Semantic.DL.Category.Object using ( Object ; _,_ ; iface )
open import Web.Semantic.DL.Category.Morphism using ( _⇒_ ; _,_ ; impl )
open import Web.Semantic.Util using ( False ; Finite ; _∈ˡ_ ; _⊕_⊕_ ; id ; _∘_ ; tt ; inode ; bnode ; enode )

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
identity (X , (xs , ∀x∙x∈xs) , A) = (False , F , F✓) where

  F : ABox Σ (X ⊕ False ⊕ X)
  F = wire xs

  F✓ : ∀ I → (I ⊨ (S , T) , A) → (I ⊕ (S , F) ⊨ (T , A))
  F✓ (I , i) ((I⊨S , I⊨T) , I⊨A) = 
    ((J , j) , ((I≲J , i≲j) , (I⊨S , J⊨F) , init) , (I⊨T , I⊨A)) where

    J = I

    j : X ⊕ False ⊕ X → Δ I
    j (inode x) = i x
    j (bnode ())
    j (enode x) = i x

    I≲J = ≲-refl I

    i≲j : ∀ x → (J ⊨ ≲-image I≲J (i x) ≈ j (inode x))
    i≲j x = ≈-refl J

    J⊨F : (J , j) ⊨a F
    J⊨F = wire-≈⁻¹ (λ x → ≈-refl I) xs

    init : Mediator (I , i) (J , j) (I≲J , i≲j) (S , F)
    init (K , k) (I≲K , i≲k) (K⊨S , K⊨F) = 
      ((J≲K , j≲k) , I≲K≋I≲J≲K , uniq) where

      J≲K = I≲K 

      j≲k : ∀ x → K ⊨ ≲-image I≲K (j x) ≈ k x
      j≲k (inode x) = i≲k x
      j≲k (bnode ())
      j≲k (enode x) = ≈-trans K (i≲k x) (wire-≈ (∀x∙x∈xs x) K⊨F)

      I≲K≋I≲J≲K : (I≲K , i≲k) ≋ (I≲J , i≲j) >> (J≲K , j≲k)
      I≲K≋I≲J≲K = λ x → ≈-refl K

      uniq : ∀ (J≲K′ : (J , j) ≲ (K , k)) → 
        ((I≲K , i≲k) ≋ (I≲J , i≲j) >> J≲K′) → ((J≲K , j≲k) ≋ J≲K′)
      uniq (J≲K′ , j≲k′) I≲K≋I≲J≲K′ = I≲K≋I≲J≲K′

