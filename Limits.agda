{-# OPTIONS --allow-unsolved-metas #-}

module Limits where

open import Library
open import Naturals
open import Functors
open import Functors.Constant
open import Categories

open Cat 
open Fun

private
  variable
    a b c d : Level
    --C D : Cat {a} {b}

{- Límites -}

{- Se define a un cono como un conjunto de flechas
que van desde una cúspide (un objeto de D) a objetos de la categoría D. -}

record Cone (C : Cat {a} {b}) (D : Cat {c} {d}) (F : Fun C D) : Set (a ⊔ b ⊔ c ⊔ d) where
  constructor cono
  open Cat D using () renaming (_∙_ to _∙D_)
  field 
    Apex : Obj D
    --ψ : {X : Obj D} → NatT (K X) F
    --ψ : NatT (K Apex) F
    ψ : ∀ (X : Obj C) → Hom D Apex (OMap F X)
    law : ∀ {X Y : Obj C} (f : Hom C X Y) → (HMap F f) ∙D ψ X ≅ ψ Y

open Cone

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
open import Relation.Binary.PropositionalEquality hiding (cong)

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
-- definir cat vacia (iso al terminal) y cat 2 (iso al producto)

empty : Cat {lzero} {lzero}
empty = 
  record
    { Obj = ⊥
    ; Hom = HomEmpty
    ; iden = IdEmpty
    ; _∙_ = CompEmpty
    ; idl = IdLEmpty
    ; idr = IdREmpty
    ; ass = AssEmpty
    }
  where HomEmpty : ⊥ → ⊥ → Set
        HomEmpty () q 
        IdEmpty : {X : ⊥} → HomEmpty X X
        IdEmpty {()}
        CompEmpty : {X Y Z : ⊥} → HomEmpty Y Z → HomEmpty X Y → HomEmpty X Z
        CompEmpty {()}
        IdLEmpty : {X Y : ⊥} {f : HomEmpty X Y} → CompEmpty IdEmpty f ≅ f
        IdLEmpty {()}
        IdREmpty : {X Y : ⊥} {f : HomEmpty X Y} → CompEmpty f IdEmpty ≅ f
        IdREmpty {()}
        AssEmpty : {W X Y Z : ⊥} {f : HomEmpty Y Z} {g : HomEmpty X Y}{h : HomEmpty W X} →
          CompEmpty (CompEmpty f g) h ≅ CompEmpty f (CompEmpty g h)
        AssEmpty {()}


{- Un límite es el objeto terminal de la categoría de conos. -}

open import Categories.Terminal

-- module Limite {C : Cat {a} {b}} {D : Cat {c} {d}}{F : Fun C D}
--   (Co : Obj (Cones {C = C} {D} {F}) )(hasTerminal : Terminal Cones Co) where

record Limit (C : Cat {a} {b}) (D : Cat {c} {d}) (F : Fun C D) : Set (lsuc (a ⊔ b ⊔ c ⊔ d)) where
  constructor limite
  field
    conoLimite : Obj (Cones C D F)
    terminal : Terminal (Cones C D F) conoLimite

{- Un objeto terminal es un límite.
Se demuestra que hay un isomorfimo entre el límite y la categoría vacía. -}

module Empty-lim {D : Cat {c} {d}} (T : Obj D) (hasTerminal : Terminal D T) where
  F : Fun empty D
  F = functor (oMap) (hMap) fId fComp
      where open Cat D using () renaming (Hom to HomD ; _∙_ to _∙D_)
            oMap : ⊥ → Obj D
            oMap ()
            hMap : {X Y : ⊥} → Hom empty X Y → HomD (oMap X) (oMap Y)
            hMap {()} {Y}
            fId : {X : ⊥} → hMap (iden empty) ≅ iden D {oMap X}
            fId {()}
            fComp : {X Y Z : ⊥} {f : Hom empty Y Z} {g : Hom empty X Y} → 
              hMap {X} {Z} (_∙_ empty f g) ≅ (D ∙ hMap f) (hMap g)
            fComp {()} {Y} {Z}

  lim-empty : Limit empty D F
  lim-empty = limite (cono T ψ-⊥ law-⊥) {!   !}
    where open Cat D using () renaming (Hom to HomD ; _∙_ to _∙D_)
          open Terminal
          ψ-⊥ : (X : ⊥) → HomD T (OMap F X)
          ψ-⊥ = λ {()}
          law-⊥ : {X Y : ⊥} (f : Hom empty X Y) → HMap F {X} {Y} f ∙D ψ-⊥ X ≅ ψ-⊥ Y
          law-⊥ {()} {Y}
          conoM-law : {X : Obj empty} {Co : Cone empty D F} → ψ-⊥ X ∙D (t hasTerminal) ≅ ψ Co X
          conoM-law {()}
          term-t : {X : Cone empty D F} → ConeMorph X (cono T ψ-⊥ law-⊥)
          term-t {X} = conoM (t hasTerminal) (conoM-law {Co = X})
          term-⊥ : Terminal (Cones empty D F) (cono T ψ-⊥ (λ {X} {Y} → law-⊥))
          term-⊥ = term term-t {!   !}
    -- Hacer con where