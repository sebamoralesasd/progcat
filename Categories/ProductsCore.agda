open import Library hiding (_×_ ; swap)
open import Categories

module Categories.ProductsCore {l}{m}(C : Cat {l}{m}) where

open Cat C

record ProductsCore (A B : Obj) : Set (l ⊔ m)
  where
  constructor prodCore
  field A×B : Obj
        π₁ : Hom (A×B) A
        π₂ : Hom (A×B) B
        ⟨_,_⟩ : ∀{C}(f : Hom C A) → (g : Hom C B) → Hom C (A×B)
        law1 : ∀{C}{f : Hom C A}{g} → π₁ ∙ ⟨ f , g ⟩ ≅ f
        law2 : ∀{C}{f : Hom C A}{g} → π₂ ∙ ⟨ f , g ⟩ ≅ g
        law3 : ∀{C}{f : Hom C A}{g : Hom C B}{h : Hom C (A×B)} →
               π₁ ∙ h ≅ f → π₂ ∙ h ≅ g → h ≅ ⟨ f , g ⟩