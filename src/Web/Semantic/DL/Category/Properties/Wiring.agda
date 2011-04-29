open import Data.Product using ( _,_ ; proj₁ ; proj₂ )
open import Data.Sum using ( inj₁ ; inj₂ )
open import Relation.Unary using ( _⊆_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; cong )
open import Web.Semantic.DL.ABox using ( ε ; _,_ ; _∼_ ; _∈₁_ ; _∈₂_ ; ⟨ABox⟩ ; Assertions )
open import Web.Semantic.DL.ABox.Interp using ( ⌊_⌋ ; ind )
open import Web.Semantic.DL.ABox.Model using ( ⊨a-impl-⊨b ; ⟨ABox⟩-Assertions )
open import Web.Semantic.DL.Category.Composition using ( _∙_ )
open import Web.Semantic.DL.Category.Object using ( Object ; _,_ ; IN ; fin ; iface )
open import Web.Semantic.DL.Category.Morphism using ( _⇒_ ; _⊑_ ; _≣_ ; _,_ )  
open import Web.Semantic.DL.Category.Properties.Composition.RespectsEquiv using ( compose-resp-≣ )
open import Web.Semantic.DL.Category.Properties.Composition.RespectsWiring using ( compose-resp-wiring )
open import Web.Semantic.DL.Category.Properties.Equivalence using ( ≣-refl ; ≣-sym ; ≣-trans )
open import Web.Semantic.DL.Category.Properties.Tensor.RespectsEquiv using ( tensor-resp-≣ )
open import Web.Semantic.DL.Category.Properties.Tensor.RespectsWiring using ( tensor-resp-wiring )
open import Web.Semantic.DL.Category.Tensor using ( _⊗_ ; _⟨⊗⟩_ )
open import Web.Semantic.DL.Category.Unit using ( I )
open import Web.Semantic.DL.Category.Wiring using
  ( wiring ; wires ; wires-≈ ; wires-≈⁻¹ 
  ; identity ; symm ; assoc ; assoc⁻¹ ; unit₁ ; unit₁⁻¹ ; unit₂ ; unit₂⁻¹
  ; id✓ ; ⊎-swap✓ ; ⊎-assoc✓ ; ⊎-assoc⁻¹✓ ; inj₁✓ ; inj₂✓ ; ⊎-unit₁✓ ; ⊎-unit₂✓ )
open import Web.Semantic.DL.Signature using ( Signature )
open import Web.Semantic.DL.TBox using ( TBox )
open import Web.Semantic.DL.TBox.Interp using ( ≈-refl′ ; ≈-trans )
open import Web.Semantic.Util using
  ( id ; _∘_ ; inode ; _⟨⊎⟩_ ; ⊎-swap ; ⊎-assoc ; ⊎-assoc⁻¹ ; ⊎-unit₁ ; ⊎-unit₂ )

module Web.Semantic.DL.Category.Properties.Wiring
  {Σ : Signature} {S T : TBox Σ} where

wiring-⊑-refl : ∀ (A B : Object S T) (f g : IN B → IN A)
  (f✓ : Assertions (⟨ABox⟩ f (iface B)) ⊆ Assertions (iface A))
    (g✓ : Assertions (⟨ABox⟩ g (iface B)) ⊆ Assertions (iface A)) →
      (∀ x → f x ≡ g x) → (wiring A B f f✓ ⊑ wiring A B g g✓)
wiring-⊑-refl A B f g f✓ g✓ f≡g I I⊨STA I⊨F =
  ⊨a-impl-⊨b I (wires g (proj₁ (fin B))) 
    (wires-≈⁻¹ g 
      (λ x → ≈-trans ⌊ I ⌋
        (≈-refl′ ⌊ I ⌋ (cong (ind I ∘ inode) (sym (f≡g x))))
        (wires-≈ f (proj₂ (fin B) x) I⊨F)) 
      (proj₁ (fin B)))

wiring-≣-refl : ∀ (A B : Object S T) (f g : IN B → IN A)
  (f✓ : Assertions (⟨ABox⟩ f (iface B)) ⊆ Assertions (iface A))
    (g✓ : Assertions (⟨ABox⟩ g (iface B)) ⊆ Assertions (iface A)) →
      (∀ x → f x ≡ g x) → (wiring A B f f✓ ≣ wiring A B g g✓)
wiring-≣-refl A B f g f✓ g✓ f≡g = 
  ( wiring-⊑-refl A B f g f✓ g✓ f≡g
  , wiring-⊑-refl A B g f g✓ f✓ (λ x → sym (f≡g x)) )

∘✓ :  (A B C : Object S T) → 
  (f : IN B → IN A) → (g : IN C → IN B) → 
  (Assertions (⟨ABox⟩ f (iface B)) ⊆ Assertions (iface A)) → 
  (Assertions (⟨ABox⟩ g (iface C)) ⊆ Assertions (iface B)) → 
  (Assertions (⟨ABox⟩ (f ∘ g) (iface C)) ⊆ Assertions (iface A))
∘✓ A B (X , X∈Fin , ε) f g f✓ g✓ ()
∘✓ A B (X , X∈Fin , C₁ , C₂) f g f✓ g✓ (inj₁ a∈C₁) = ∘✓ A B (X , X∈Fin , C₁) f g f✓ (g✓ ∘ inj₁) a∈C₁
∘✓ A B (X , X∈Fin , C₁ , C₂) f g f✓ g✓ (inj₂ a∈C₂) = ∘✓ A B (X , X∈Fin , C₂) f g f✓ (g✓ ∘ inj₂) a∈C₂
∘✓ A B (X , X∈Fin , x ∼ y) f g f✓ g✓ refl = f✓ (⟨ABox⟩-Assertions f (iface B) (g✓ refl))
∘✓ A B (X , X∈Fin , x ∈₁ c) f g f✓ g✓ refl = f✓ (⟨ABox⟩-Assertions f (iface B) (g✓ refl))
∘✓ A B (X , X∈Fin , (x , y) ∈₂ r) f g f✓ g✓ refl = f✓ (⟨ABox⟩-Assertions f (iface B) (g✓ refl))

⟨⊎⟩✓ : (A₁ A₂ B₁ B₂ : Object S T) → 
  (f₁ : IN B₁ → IN A₁) → (f₂ : IN B₂ → IN A₂) → 
  (Assertions (⟨ABox⟩ f₁ (iface B₁)) ⊆ Assertions (iface A₁)) → 
  (Assertions (⟨ABox⟩ f₂ (iface B₂)) ⊆ Assertions (iface A₂)) → 
  (Assertions (⟨ABox⟩ (f₁ ⟨⊎⟩ f₂) (iface (B₁ ⊗ B₂))) ⊆ Assertions (iface (A₁ ⊗ A₂)))
⟨⊎⟩✓ A₁ A₂ (X₁ , X₁∈Fin , ε) B₂ f₁ f₂ f₁✓ f₂✓ (inj₁ ()) 
⟨⊎⟩✓ A₁ A₂ (X₁ , X₁∈Fin , B₁₁ , B₁₂) B₂ f₁ f₂ f₁✓ f₂✓ (inj₁ (inj₁ b∈B₁₁)) = 
  ⟨⊎⟩✓ A₁ A₂ (X₁ , X₁∈Fin , B₁₁) B₂ f₁ f₂ (f₁✓ ∘ inj₁) f₂✓ (inj₁ b∈B₁₁)
⟨⊎⟩✓ A₁ A₂ (X₁ , X₁∈Fin , B₁₁ , B₁₂) B₂ f₁ f₂ f₁✓ f₂✓ (inj₁ (inj₂ b∈B₁₂)) = 
  ⟨⊎⟩✓ A₁ A₂ (X₁ , X₁∈Fin , B₁₂) B₂ f₁ f₂ (f₁✓ ∘ inj₂) f₂✓ (inj₁ b∈B₁₂) 
⟨⊎⟩✓ A₁ A₂ (X₁ , X₁∈Fin , x ∼ y) B₂ f₁ f₂ f₁✓ f₂✓ (inj₁ refl) = 
  inj₁ (⟨ABox⟩-Assertions inj₁ (iface A₁) (f₁✓ refl)) 
⟨⊎⟩✓ A₁ A₂ (X₁ , X₁∈Fin , x ∈₁ c) B₂ f₁ f₂ f₁✓ f₂✓ (inj₁ refl) = 
  inj₁ (⟨ABox⟩-Assertions inj₁ (iface A₁) (f₁✓ refl)) 
⟨⊎⟩✓ A₁ A₂ (X₁ , X₁∈Fin , (x , y) ∈₂ r) B₂ f₁ f₂ f₁✓ f₂✓ (inj₁ refl) = 
  inj₁ (⟨ABox⟩-Assertions inj₁ (iface A₁) (f₁✓ refl)) 
⟨⊎⟩✓ A₁ A₂ B₁ (X₂ , X₂∈Fin , ε) f₁ f₂ f₁✓ f₂✓ (inj₂ ()) 
⟨⊎⟩✓ A₁ A₂ B₁ (X₂ , X₂∈Fin , B₂₁ , B₂₂) f₁ f₂ f₁✓ f₂✓ (inj₂ (inj₁ b∈B₂₁)) = 
  ⟨⊎⟩✓ A₁ A₂ B₁ (X₂ , X₂∈Fin , B₂₁) f₁ f₂ f₁✓ (f₂✓ ∘ inj₁) (inj₂ b∈B₂₁)
⟨⊎⟩✓ A₁ A₂ B₁ (X₂ , X₂∈Fin , B₂₁ , B₂₂) f₁ f₂ f₁✓ f₂✓ (inj₂ (inj₂ b∈B₂₂)) = 
  ⟨⊎⟩✓ A₁ A₂ B₁ (X₂ , X₂∈Fin , B₂₂) f₁ f₂ f₁✓ (f₂✓ ∘ inj₂) (inj₂ b∈B₂₂) 
⟨⊎⟩✓ A₁ A₂ B₁ (X₂ , X₂∈Fin , x ∼ y) f₁ f₂ f₁✓ f₂✓ (inj₂ refl) =
  inj₂ (⟨ABox⟩-Assertions inj₂ (iface A₂) (f₂✓ refl)) 
⟨⊎⟩✓ A₁ A₂ B₁ (X₂ , X₂∈Fin , x ∈₁ c) f₁ f₂ f₁✓ f₂✓ (inj₂ refl) =
  inj₂ (⟨ABox⟩-Assertions inj₂ (iface A₂) (f₂✓ refl)) 
⟨⊎⟩✓ A₁ A₂ B₁ (X₂ , X₂∈Fin , (x , y) ∈₂ r) f₁ f₂ f₁✓ f₂✓ (inj₂ refl) =
  inj₂ (⟨ABox⟩-Assertions inj₂ (iface A₂) (f₂✓ refl)) 

data Rewrite : (A B : Object S T) (F : A ⇒ B) (f : IN B → IN A) →
  (Assertions (⟨ABox⟩ f (iface B)) ⊆ Assertions (iface A)) → Set₁ where
    rewrite-wiring : ∀ A B f (f✓ : Assertions (⟨ABox⟩ f (iface B)) ⊆ Assertions (iface A)) →
      Rewrite A B (wiring A B f f✓) f f✓
    rewrite-compose : ∀ {A B C F G f g} 
      {f✓ : Assertions (⟨ABox⟩ f (iface B)) ⊆ Assertions (iface A)} 
        {g✓ : Assertions (⟨ABox⟩ g (iface C)) ⊆ Assertions (iface B)} →
      Rewrite A B F f f✓ → Rewrite B C G g g✓ → Rewrite A C (F ∙ G) (f ∘ g) (∘✓ A B C f g f✓ g✓)
    rewrite-tensor : ∀ {A₁ A₂ B₁ B₂ F₁ F₂ f₁ f₂}
      {f₁✓ : Assertions (⟨ABox⟩ f₁ (iface B₁)) ⊆ Assertions (iface A₁)}
        {f₂✓ : Assertions (⟨ABox⟩ f₂ (iface B₂)) ⊆ Assertions (iface A₂)} →
          Rewrite A₁ B₁ F₁ f₁ f₁✓ → Rewrite A₂ B₂ F₂ f₂ f₂✓ → 
            Rewrite (A₁ ⊗ A₂) (B₁ ⊗ B₂) (F₁ ⟨⊗⟩ F₂) (f₁ ⟨⊎⟩ f₂) (⟨⊎⟩✓ A₁ A₂ B₁ B₂ f₁ f₂ f₁✓ f₂✓)

rewrite-identity : ∀ A → Rewrite A A (identity A) id (id✓ A)
rewrite-identity A = rewrite-wiring A A id (id✓ A)
    
rewrite-symm : ∀ A B → Rewrite (A ⊗ B) (B ⊗ A) (symm A B) ⊎-swap (⊎-swap✓ A B)
rewrite-symm A B = rewrite-wiring (A ⊗ B) (B ⊗ A) ⊎-swap (⊎-swap✓ A B)

rewrite-assoc : ∀ A B C → Rewrite ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C)) (assoc A B C) ⊎-assoc⁻¹ (⊎-assoc⁻¹✓ A B C)
rewrite-assoc A B C = rewrite-wiring ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C)) ⊎-assoc⁻¹ (⊎-assoc⁻¹✓ A B C)

rewrite-assoc⁻¹ : ∀ A B C → Rewrite (A ⊗ (B ⊗ C)) ((A ⊗ B) ⊗ C) (assoc⁻¹ A B C) ⊎-assoc (⊎-assoc✓ A B C)
rewrite-assoc⁻¹ A B C = rewrite-wiring (A ⊗ (B ⊗ C)) ((A ⊗ B) ⊗ C) ⊎-assoc (⊎-assoc✓ A B C)

rewrite-unit₁ : ∀ A → Rewrite (I ⊗ A) A (unit₁ A) inj₂ (inj₂✓ A)
rewrite-unit₁ A = rewrite-wiring (I ⊗ A) A inj₂ (inj₂✓ A)

rewrite-unit₁⁻¹ : ∀ A → Rewrite A (I ⊗ A) (unit₁⁻¹ A) ⊎-unit₁ (⊎-unit₁✓ A)
rewrite-unit₁⁻¹ A = rewrite-wiring A (I ⊗ A) ⊎-unit₁ (⊎-unit₁✓ A)

rewrite-unit₂ : ∀ A → Rewrite (A ⊗ I) A (unit₂ A) inj₁ (inj₁✓ A)
rewrite-unit₂ A = rewrite-wiring (A ⊗ I) A inj₁ (inj₁✓ A)

rewrite-unit₂⁻¹ : ∀ A → Rewrite A (A ⊗ I) (unit₂⁻¹ A) ⊎-unit₂ (⊎-unit₂✓ A)
rewrite-unit₂⁻¹ A = rewrite-wiring A (A ⊗ I) ⊎-unit₂ (⊎-unit₂✓ A)

rewriting : ∀ {A B F G f g}
  {f✓ : Assertions (⟨ABox⟩ f (iface B)) ⊆ Assertions (iface A)} 
    {g✓ : Assertions (⟨ABox⟩ g (iface B)) ⊆ Assertions (iface A)} →
      (Rewrite A B F f f✓) → (∀ x → f x ≡ g x) → (Rewrite A B G g g✓) →
        (F ≣ G)
rewriting {A} {B} {F} {G} {f} {g} {f✓} {g✓} F⇓f f≡g G⇓g = 
  ≣-trans (lemma F⇓f) 
    (≣-trans (wiring-≣-refl A B f g f✓ g✓ f≡g)
      (≣-sym (lemma G⇓g))) where

  lemma :  ∀ {A B F f}
    {f✓ : Assertions (⟨ABox⟩ f (iface B)) ⊆ Assertions (iface A)} →
      (Rewrite A B F f f✓) →
        (F ≣ wiring A B f f✓)
  lemma (rewrite-wiring A B f f✓) = ≣-refl (wiring A B f f✓)
  lemma (rewrite-compose {A} {B} {C} {F} {G} {f} {g} {f✓} {g✓} F⇓f G⇓g) = 
    ≣-trans (compose-resp-≣ (lemma F⇓f) (lemma G⇓g))
      (compose-resp-wiring A B C f f✓ g g✓ (f ∘ g) 
        (∘✓ A B C f g f✓ g✓) (λ x → refl))
  lemma (rewrite-tensor {A₁} {A₂} {B₁} {B₂} {F₁} {F₂} {f₁} {f₂} {f₁✓} {f₂✓} F₁⇓f₁ F₂⇓f₂) = 
    ≣-trans (tensor-resp-≣ (lemma F₁⇓f₁) (lemma F₂⇓f₂)) 
      (tensor-resp-wiring A₁ A₂ B₁ B₂ f₁ f₁✓ f₂ f₂✓ (f₁ ⟨⊎⟩ f₂) 
        (⟨⊎⟩✓ A₁ A₂ B₁ B₂ f₁ f₂ f₁✓ f₂✓) (λ x → refl) (λ x → refl))
