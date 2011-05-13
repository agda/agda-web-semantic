open import Data.List using ( List ; [] ; _∷_ )
open import Data.List.Any using ( here ; there )
open import Data.Product using ( _,_ ; proj₁ ; proj₂ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality using
  ( refl ; sym ; trans ; subst₂ )
open import Relation.Unary using ( _∈_ ; _⊆_ )
open import Web.Semantic.DL.ABox using
  ( ABox ; ε ; _,_ ; _∼_ ; ⟨ABox⟩ ; Assertions
  ; ⟨ABox⟩-resp-id ; ⟨ABox⟩-resp-∘ ; ⟨ABox⟩-resp-∘² )
open import Web.Semantic.DL.ABox.Interp using ( Interp ; _,_ ; ⌊_⌋ ; ind ; _*_ )
open import Web.Semantic.DL.ABox.Interp.Morphism using ( _,_ )
open import Web.Semantic.DL.ABox.Model using
  ( _⊨a_ ; *-resp-⟨ABox⟩ ; ⊨a-resp-⊇ )
open import Web.Semantic.DL.Category.Object using
  ( Object ; _,_ ; IN ; fin ; iface )
open import Web.Semantic.DL.Category.Morphism using
  ( _⇒_ ; _,_ ; BN ; impl )
open import Web.Semantic.DL.Category.Tensor using ( _⊗_ ) 
open import Web.Semantic.DL.Category.Unit using ( I ) 
open import Web.Semantic.DL.Integrity using
  ( Unique ; Mediator ; Initial ; _⊕_⊨_ ; _,_ )
open import Web.Semantic.DL.KB using ( _,_ )
open import Web.Semantic.DL.KB.Model using ( _⊨_ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox ; _,_ )
open import Web.Semantic.DL.TBox.Interp using
  ( _⊨_≈_ ; ≈-refl ; ≈-sym ; ≈-trans )
open import Web.Semantic.DL.TBox.Interp.Morphism using ( ≲-refl ; ≲-image )
open import Web.Semantic.DL.TBox.Model using ( _⊨t_ )
open import Web.Semantic.Util using 
  ( id ; _∘_ ; False ; tt ; ⊎-swap ; ⊎-assoc ; ⊎-assoc⁻¹ ; ⊎-unit₁ ; ⊎-unit₂
  ; _∈ˡ_ ; _⊕_⊕_ ; inode ; bnode ; enode ) 

module Web.Semantic.DL.Category.Wiring {Σ : Signature} where

wires : ∀ {X Y} → (Y → X) → List Y → ABox Σ (X ⊕ False ⊕ Y)
wires f [] = ε
wires f (y ∷ ys) = (inode (f y) ∼ enode y , wires f ys)

wires-≈ : ∀ {X Y y ys I} (f : Y → X) → (y ∈ˡ ys) → (I ⊨a wires f ys) →
  (⌊ I ⌋ ⊨ ind I (inode (f y)) ≈ ind I (enode y))
wires-≈ f (here refl)  (x≈y , xs≈ys) = x≈y
wires-≈ f (there y∈ys) (x≈y , xs≈ys) = wires-≈ f y∈ys xs≈ys

wires-≈⁻¹ : ∀ {X Y I} (f : Y → X) →
  (∀ y → ⌊ I ⌋ ⊨ ind I (inode (f y)) ≈ ind I (enode y)) →
    ∀ ys → (I ⊨a wires f ys)
wires-≈⁻¹ f ∀y∙x≈y []       = tt
wires-≈⁻¹ f ∀y∙x≈y (y ∷ ys) = (∀y∙x≈y y , wires-≈⁻¹ f ∀y∙x≈y ys)

wired : ∀ {X Y} → (Y → X) → (X ⊕ False ⊕ Y) → X
wired f (inode x) = x
wired f (bnode ())
wired f (enode y) = f y

wired-init : ∀ {X Y} (f : Y → X) ys → (∀ y → y ∈ˡ ys) →
  (I : Interp Σ X) → (S : TBox Σ) → (⌊ I ⌋ ⊨t S) →
    (wired f * I ∈ Initial I (S , wires f ys))
wired-init f ys ∀y∙y∈ys (I , i) S I⊨S = 
  ( (≲-refl I , λ x → ≈-refl I) 
  , (I⊨S , wires-≈⁻¹ f (λ x → ≈-refl I) ys)
  , mediator ) where

  mediator : Mediator (I , i) (I , i ∘ wired f) 
    (≲-refl I , λ x → ≈-refl I) (S , wires f ys)
  mediator (K , k) (I≲K , i≲k) (K⊨S , K⊨F) = 
    ((I≲K , j≲k) , (λ x → ≈-refl K) , uniq ) where

    j≲k : ∀ x → K ⊨ ≲-image I≲K (i (wired f x)) ≈ k x
    j≲k (inode x) = i≲k x
    j≲k (bnode ())
    j≲k (enode y) = ≈-trans K (i≲k (f y)) (wires-≈ f (∀y∙y∈ys y) K⊨F)
  
    uniq : Unique (I , i) (I , i ∘ wired f) (K , k)
      (≲-refl I , λ x → ≈-refl I) (I≲K , i≲k)
    uniq J≲₁K J≲₂K I≲K≋I≲J≲₁K I≲K≋I≲J≲₂K x = 
      ≈-trans K (≈-sym K (I≲K≋I≲J≲₁K x)) (I≲K≋I≲J≲₂K x)

wires✓ : ∀ {X Y ys} (f : Y → X) → (∀ y → y ∈ˡ ys) → 
  (S T : TBox Σ) (A : ABox Σ X) (B : ABox Σ Y) → 
    (Assertions (⟨ABox⟩ f B) ⊆ Assertions A) →
      (I : Interp Σ X) → (I ⊨ (S , T) , A) → (I ⊕ S , wires f ys ⊨ T , B)
wires✓ {X} {Y} {ys} f ∀y∙y∈ys S T A B B⊆A I I⊨STA = 
  (J , J-init , (J⊨T , J⊨B)) where

  J : Interp Σ (X ⊕ False ⊕ Y)
  J = wired f * I

  J⊨T : ⌊ J ⌋ ⊨t T
  J⊨T = proj₂ (proj₁ I⊨STA)

  J⊨B : enode * J ⊨a B
  J⊨B = *-resp-⟨ABox⟩ f I B (⊨a-resp-⊇ I (⟨ABox⟩ f B) A B⊆A (proj₂ I⊨STA))

  J-init : J ∈ Initial I (S , wires f ys)
  J-init = wired-init f ys ∀y∙y∈ys I S (proj₁ (proj₁ I⊨STA))

wiring-impl : ∀ {S T : TBox Σ} → (A B : Object S T) (f : IN B → IN A) → 
  ABox Σ (IN A ⊕ False ⊕ IN B)
wiring-impl A B f =
  wires f (proj₁ (fin B))

wiring-impl✓ : ∀ {S T : TBox Σ} → (A B : Object S T) (f : IN B → IN A) → 
  (Assertions (⟨ABox⟩ f (iface B)) ⊆ Assertions (iface A)) → 
    ∀ I → (I ⊨ (S , T) , iface A) → (I ⊕ (S , wiring-impl A B f) ⊨ (T , iface B))
wiring-impl✓ {S} {T} (X , X∈Fin , A) (Y , Y∈Fin , B) f B⊆A =
  wires✓ f (proj₂ Y∈Fin) S T A B B⊆A

wiring : ∀ {S T : TBox Σ} → (A B : Object S T) (f : IN B → IN A) → 
  (Assertions (⟨ABox⟩ f (iface B)) ⊆ Assertions (iface A)) → 
    (A ⇒ B)
wiring A B f B⊆A = 
  ( False , wiring-impl A B f , wiring-impl✓ A B f B⊆A )

id✓ : ∀ {S T : TBox Σ} → (A : Object S T) → 
  (Assertions (⟨ABox⟩ id (iface A)) ⊆ Assertions (iface A))
id✓ A = subst₂ Assertions (⟨ABox⟩-resp-id (iface A)) refl

identity : ∀ {S T : TBox Σ} → (A : Object S T) → (A ⇒ A)
identity A = wiring A A id (id✓ A)

⊎-swap✓ : ∀ {S T : TBox Σ} → (A B : Object S T) → 
  Assertions (⟨ABox⟩ ⊎-swap (iface (B ⊗ A))) ⊆ Assertions (iface (A ⊗ B))
⊎-swap✓ A B (inj₁ b∈B) = 
  inj₂ (subst₂ Assertions (⟨ABox⟩-resp-∘ ⊎-swap inj₁ (iface B)) refl b∈B)
⊎-swap✓ A B (inj₂ a∈A) = 
  inj₁ (subst₂ Assertions (⟨ABox⟩-resp-∘ ⊎-swap inj₂ (iface A)) refl a∈A)

symm : ∀ {S T : TBox Σ} → (A B : Object S T) → ((A ⊗ B) ⇒ (B ⊗ A))
symm A B = wiring (A ⊗ B) (B ⊗ A) ⊎-swap (⊎-swap✓ A B)

⊎-assoc⁻¹✓ : ∀ {S T : TBox Σ} → (A B C : Object S T) →
  (Assertions (⟨ABox⟩ ⊎-assoc⁻¹ (iface (A ⊗ (B ⊗ C))))) ⊆
    (Assertions (iface ((A ⊗ B) ⊗ C)))
⊎-assoc⁻¹✓ A B C (inj₁ a∈A) = inj₁ (inj₁ (subst₂ Assertions 
  (trans (⟨ABox⟩-resp-∘ ⊎-assoc⁻¹ inj₁ (iface A)) 
    (sym (⟨ABox⟩-resp-∘ inj₁ inj₁ (iface A))))
  refl a∈A))
⊎-assoc⁻¹✓ A B C (inj₂ (inj₁ b∈B)) = inj₁ (inj₂ (subst₂ Assertions 
  (trans (⟨ABox⟩-resp-∘² ⊎-assoc⁻¹ inj₂ inj₁ (iface B)) 
    (sym (⟨ABox⟩-resp-∘ inj₁ inj₂ (iface B)))) 
  refl b∈B))
⊎-assoc⁻¹✓ A B C (inj₂ (inj₂ c∈C)) = inj₂ (subst₂ Assertions 
  (⟨ABox⟩-resp-∘² ⊎-assoc⁻¹ inj₂ inj₂ (iface C))
  refl c∈C)

assoc : ∀ {S T : TBox Σ} → (A B C : Object S T) →
  (((A ⊗ B) ⊗ C) ⇒ (A ⊗ (B ⊗ C)))
assoc A B C = wiring ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C)) ⊎-assoc⁻¹ (⊎-assoc⁻¹✓ A B C)

⊎-assoc✓ : ∀ {S T : TBox Σ} → (A B C : Object S T) →
  (Assertions (⟨ABox⟩ ⊎-assoc (iface ((A ⊗ B) ⊗ C)))) ⊆
    (Assertions (iface (A ⊗ (B ⊗ C))))
⊎-assoc✓ A B C (inj₁ (inj₁ a∈A)) = inj₁ (subst₂ Assertions 
  (⟨ABox⟩-resp-∘² ⊎-assoc inj₁ inj₁ (iface A)) 
  refl a∈A)
⊎-assoc✓ A B C (inj₁ (inj₂ b∈B)) = inj₂ (inj₁ (subst₂ Assertions 
  (trans (⟨ABox⟩-resp-∘² ⊎-assoc inj₁ inj₂ (iface B))
    (sym (⟨ABox⟩-resp-∘ inj₂ inj₁ (iface B)))) 
  refl b∈B))
⊎-assoc✓ A B C (inj₂ c∈C) = inj₂ (inj₂ (subst₂ Assertions
  (trans (⟨ABox⟩-resp-∘ ⊎-assoc inj₂ (iface C))
    (sym (⟨ABox⟩-resp-∘ inj₂ inj₂ (iface C))))
  refl c∈C))

assoc⁻¹ : ∀ {S T : TBox Σ} → (A B C : Object S T) →
  ((A ⊗ (B ⊗ C)) ⇒ ((A ⊗ B) ⊗ C))
assoc⁻¹ A B C = wiring (A ⊗ (B ⊗ C)) ((A ⊗ B) ⊗ C) ⊎-assoc (⊎-assoc✓ A B C)

inj₂✓ : ∀ {S T : TBox Σ} → (A : Object S T) →
  (Assertions (⟨ABox⟩ inj₂ (iface A))) ⊆
    (Assertions (iface (I ⊗ A)))
inj₂✓ A = inj₂

unit₁ : ∀ {S T : TBox Σ} (A : Object S T) → ((I ⊗ A) ⇒ A)
unit₁ A = wiring (I ⊗ A) A inj₂ (inj₂✓ A)

⊎-unit₁✓ : ∀ {S T : TBox Σ} → (A : Object S T) →
  Assertions (⟨ABox⟩ ⊎-unit₁ (iface (I ⊗ A))) ⊆ Assertions (iface A)
⊎-unit₁✓ A (inj₁ ())
⊎-unit₁✓ A (inj₂ a∈A) = subst₂ Assertions 
  (trans (⟨ABox⟩-resp-∘ ⊎-unit₁ inj₂ (iface A)) (⟨ABox⟩-resp-id (iface A)))
  refl a∈A

unit₁⁻¹ : ∀ {S T : TBox Σ} (A : Object S T) → (A ⇒ (I ⊗ A))
unit₁⁻¹ A = wiring A (I ⊗ A) ⊎-unit₁ (⊎-unit₁✓ A)

inj₁✓ : ∀ {S T : TBox Σ} → (A : Object S T) →
  (Assertions (⟨ABox⟩ inj₁ (iface A))) ⊆
    (Assertions (iface (A ⊗ I)))
inj₁✓ A = inj₁

unit₂ : ∀ {S T : TBox Σ} (A : Object S T) → ((A ⊗ I) ⇒ A)
unit₂ A = wiring (A ⊗ I) A inj₁ (inj₁✓ A)

⊎-unit₂✓ : ∀ {S T : TBox Σ} (A : Object S T) → 
  Assertions (⟨ABox⟩ ⊎-unit₂ (iface (A ⊗ I))) ⊆ Assertions (iface A)
⊎-unit₂✓ A (inj₁ a∈A) = subst₂ Assertions 
  (trans (⟨ABox⟩-resp-∘ ⊎-unit₂ inj₁ (iface A)) (⟨ABox⟩-resp-id (iface A)))
  refl a∈A
⊎-unit₂✓ A (inj₂ ())

unit₂⁻¹ : ∀ {S T : TBox Σ} (A : Object S T) → (A ⇒ (A ⊗ I))
unit₂⁻¹ A = wiring A (A ⊗ I) ⊎-unit₂ (⊎-unit₂✓ A)
