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

record Limit (C : Cat {a} {b}) (D : Cat {c} {d}) (F : Fun C D) : Set (lsuc (a ⊔ b ⊔ c ⊔ d)) where
  constructor limite
  field
    conoLim : Obj (Cones C D F)
    conoLim-terminal : Terminal (Cones C D F) conoLim

open Limit


{- Un objeto terminal es un límite.
Se demuestra que hay un isomorfimo entre el límite y la categoría vacía. -}

module Lim-terminal {D : Cat {c} {d}}{F : Fun empty D}(L : Limit empty D F) where

  open Limit L renaming (conoLim to conoL ; conoLim-terminal to conoL-t)

  term-is-lim : Terminal D (Apex conoL)
  term-is-lim = term t-term law-term
    where open Cat D using () renaming (Hom to HomD ; _∙_ to _∙D_)
          open Terminal
          conoN : (Na : Obj D) → Cone empty D F
          conoN Na = cono Na conoN-ψ conoN-law
            where conoN-ψ : (X : ⊥) → HomD Na (OMap F X)
                  conoN-ψ ()
                  conoN-law : {X Y : ⊥} (f : Hom empty X Y) → HMap F f ∙D conoN-ψ X ≅ conoN-ψ Y
                  conoN-law {()} {Y}
          t-term : {N : Obj D} → HomD N (Apex conoL)
          t-term {N} = CHom (t conoL-t {conoN N})
          law-term : {X : Obj D} {f : HomD X (Apex conoL)} → t-term {X} ≅ f
          law-term {X} {f} = 
            proof 
              t-term {X}
              ≅⟨ refl ⟩
              -- t conoL-t {conoN X} == Hom (Cones empty D F) (conoN X) conoL
              CHom (t conoL-t {conoN X})
              ≅⟨ cong CHom (law conoL-t {conoN X} {asd}) ⟩
              f
              ∎
                where
                  asd1 : (Od : Obj D){X = X₁ : ⊥} → ψ conoL X₁ ∙D f ≅ ψ (conoN Od) X₁
                  asd1 (Od) {()}
                  asd : ConeMorph (conoN X) (conoL)
                  asd = conoM f (asd1 (X))



{- Un producto es un límite. 
Se construye un producto a partir del límite que se conforma a partir de la categoría 2 -}

data Bool : Set where
        tt : Bool
        ff : Bool

open import Categories.Discrete

-- Renombrar a categoria 2
Prod : Cat
Prod = Discrete (Bool)

FunProd : (D : Cat {c} {d}) (A B : Obj D) → Fun Prod D
FunProd D A B = 
  functor oMap hMap refl (λ {X} {Y} {Z} {f} {g} → fComp {X} {Y} {Z} {f} {g})
    where
      oMap : Obj Prod → Obj D
      oMap tt = A
      oMap ff = B
      hMap : {X Y : Obj Prod} → Hom Prod X Y → Hom D (oMap X) (oMap Y)
      hMap {X} {.X} refl = iden D
      fComp : {X Y Z : Obj Prod} {f : Hom Prod Y Z} {g : Hom Prod X Y} → hMap ((Prod ∙ f) g) ≅ (D ∙ hMap f) (hMap g)
      fComp {X} {.X} {.X} {refl} {refl} = Library.sym (idr D)



module Lim-product {D : Cat {c} {d}}{A B : Obj D}(L : Limit Prod D (FunProd D A B)) where

  open import Categories.Products D
  open Limit L renaming (conoLim to conoP ; conoLim-terminal to conoP-t)

  F : Fun Prod D
  F = FunProd D A B
  prod-is-lim : Products
  prod-is-lim = 
    prod times {!   !} {!   !} {!   !} {!   !} {!   !} {!   !}
      where
        times : Obj D → Obj D → Obj D
        times _ _ = Apex conoP
        proj1 : {X : Obj D} {Y : Obj D} → Hom D (Apex conoP) X
        proj1 {X} {Y} = {!   !}