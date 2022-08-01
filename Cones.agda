module Cones where

-- open import Naturals
-- open import Functors.Constant
open import Library
open import Functors
open import Categories

open Cat
open Fun

private
  variable
    a b c d : Level


{- Se define a un cono como un conjunto de flechas
que van desde una cúspide (un objeto de D) a objetos de la categoría D. -}

record Cone (C : Cat {a} {b}) (D : Cat {c} {d}) (F : Fun C D) : Set (a ⊔ b ⊔ c ⊔ d) where
  constructor cono
  open Cat D using () renaming (_∙_ to _∙D_)
  field
    Apex : Obj D
    --ψ : NatT (K Apex) F
    ψ : ∀ (X : Obj C) → Hom D Apex (OMap F X)
    law : ∀ {X Y : Obj C} (f : Hom C X Y) → (HMap F f) ∙D ψ X ≅ ψ Y

open Cone


{- Damos todas las definiciones necesarias para -valga la
  redundancia- definir la categoría de conos. -}

{- Morfismos de la categoría de conos -}
record ConeMorph {C : Cat {a} {b}} {D : Cat {c} {d}} {F : Fun C D}
  (Ca Cb : Cone C D F) : Set (lsuc (a ⊔ b ⊔ c ⊔ d)) where
  constructor conoM
  open Cat D using () renaming (Hom to HomD ; _∙_ to _∙D_)
  field
    CHom : HomD (Apex Ca) (Apex Cb)
    lawMorph : ∀{X : Obj C} → ψ Cb X ∙D CHom ≅ ψ Ca X

open ConeMorph


{- Composición de conos -}
Cone-comp : {C : Cat {a} {b}} {D : Cat {c} {d}}{F : Fun C D}{Ca Cb Cc : Cone C D F} →
  ConeMorph Cb Cc → ConeMorph Ca Cb → ConeMorph Ca Cc
Cone-comp {C = C} {D} {F} {Ca} {Cb} {Cc} bc ab
  = conoM (CHom bc ∙D CHom ab) ψ-comp
    where open Cat D using () renaming (Hom to HomD ; _∙_ to _∙D_)
          ψ-comp : {X : Obj C} → ψ Cc X ∙D CHom bc ∙D CHom ab ≅ ψ Ca X
          ψ-comp {X} = proof
                   ψ Cc X ∙D CHom bc ∙D CHom ab
                   ≅⟨ refl ⟩
                   ψ Cc X ∙D (CHom bc ∙D CHom ab)
                   ≅⟨ sym (ass D) ⟩
                   (ψ Cc X ∙D CHom bc) ∙D CHom ab
                   ≅⟨ congl D (lawMorph bc) ⟩
                   ψ Cb X ∙D CHom ab
                   ≅⟨ lawMorph ab ⟩
                   ψ Ca X
                   ∎

{- Definición de igualdad para morfismos de conos -}
open import Relation.Binary.PropositionalEquality hiding (cong ; sym ; trans)

{- Aplicamos irrelevancia de pruebas sobre las leyes de los morfismos .-}
ConeMorph-eq : {C : Cat {a} {b}} {D : Cat {c} {d}}{F : Fun C D}{Ca Cb : Cone C D F}
  { Cm Cm' : ConeMorph Ca Cb} →
  (CHom Cm) ≅ (CHom Cm') →
  Cm ≅ Cm'
ConeMorph-eq {C = C} {D} {F} {Ca} {Cb} {conoM chom leyM} {conoM .chom leyM'} refl
  = cong (conoM chom) (iext λ _ → ir leyM leyM')



{- Conos como una categoria -}
Cones : (C : Cat {a} {b}) (D : Cat {c} {d}) (F : Fun C D) → Cat {(a ⊔ b ⊔ c ⊔ d)} {lsuc (a ⊔ b ⊔ c ⊔ d)}
Cones C D F =
  record
    { Obj = Cone C D F
    ; Hom = ConeMorph
    ; iden = conoM (iden D) (idr D)
    ; _∙_ = Cone-comp
    ; idl = ConeMorph-eq (idl D)
    ; idr = ConeMorph-eq (idr D)
    ; ass = ConeMorph-eq (ass D)
    }
