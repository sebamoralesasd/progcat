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
open import Relation.Binary.PropositionalEquality hiding (cong ; sym ; trans)

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

{- Definición de categoría vacía -}
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
    cone-lim : Obj (Cones C D F)
    is-terminal : Terminal (Cones C D F) cone-lim

open Limit


{- Un objeto terminal es un límite.
  Se define un objeto terminal en D con el límite que se conforma a partir
  del funtor que va de la categoría vacía hacia D.
-}
module Lim-terminal {D : Cat {c} {d}}{F : Fun empty D}(L : Limit empty D F) where

  open Limit L renaming (cone-lim to conoL ; is-terminal to conoL-t)

  term-is-lim : Terminal D (Apex conoL)
  term-is-lim = term t-term law-term
    where open Cat D using () renaming (Hom to HomD ; _∙_ to _∙D_)
          open Terminal
          -- Defino otro cono sobre D para usarlo en las leyes de Terminal
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
              ≅⟨ cong CHom (law conoL-t {conoN X} {nl-morph}) ⟩
              f
              ∎
                where
                  nl-morph-aux : (Od : Obj D){X = X₁ : ⊥} → ψ conoL X₁ ∙D f ≅ ψ (conoN Od) X₁
                  nl-morph-aux (Od) {()}
                  nl-morph : ConeMorph (conoN X) (conoL)
                  nl-morph = conoM f (nl-morph-aux (X))



{- Un producto es un límite.
  Se construye un producto a partir del límite que se conforma a partir
  del funtor que va de la categoría 2 a D
-}

{- Defino dos objetos cualquiera para definir la categoría 2 -}
data Bool : Set where
        tt : Bool
        ff : Bool

open import Categories.Discrete

-- Categoría 2
Dos : Cat
Dos = Discrete (Bool)

-- Funtor que mapea a los dos objetos de 2 con dos
-- objetos (A, B) de D
FunProd : (D : Cat {c} {d}) (A B : Obj D) → Fun Dos D
FunProd D A B =
  functor oMap hMap refl (λ {X} {Y} {Z} {f} {g} → fComp {X} {Y} {Z} {f} {g})
    where open Cat D using () renaming (Hom to HomD ; _∙_ to _∙D_)
          open Library
          oMap : Obj Dos → Obj D
          oMap tt = A
          oMap ff = B
          hMap : {X Y : Obj Dos} → Hom Dos X Y → HomD (oMap X) (oMap Y)
          hMap {X} {.X} refl = iden D
          fComp : {X Y Z : Obj Dos} {f : Hom Dos Y Z} {g : Hom Dos X Y} → hMap ((Dos ∙ f) g) ≅ (hMap f) ∙D (hMap g)
          fComp {X} {.X} {.X} {refl} {refl} = sym (idr D)



module Lim-product {D : Cat {c} {d}}{A B : Obj D}(L : Limit Dos D (FunProd D A B)) where

  open import Categories.ProductsCore D
  open Limit L renaming (cone-lim to conoP ; is-terminal to conoP-t)

  F : Fun Dos D
  F = FunProd D A B

  prod-is-lim : ProductsCore A B
  prod-is-lim =
    prodCore
      (Apex conoP) proj1 proj2 ⟨_,_⟩ law1 law2 law3
      where
        open Cat D using () renaming (Hom to HomD ; _∙_ to _∙D_)
        open Terminal
        open Library
        proj1 : HomD (Apex conoP) A
        proj1 = ψ conoP tt
        proj2 : HomD (Apex conoP) B
        proj2 = ψ conoP ff
        ⟨_,_⟩ : {C : Obj D} → HomD C A → HomD C B → HomD C (Apex conoP)
        ⟨_,_⟩ {C} f g = CHom {C = Dos} {D = D} {F = F} (t conoP-t {conoN})
          where
            conoN-ψ : (X : Obj Dos) → HomD C (OMap F X)
            conoN-ψ tt = f
            conoN-ψ ff = g
            -- Los morfismos de Dos son solo las identidades sobre tt y ff
            -- (por ser categoría discreta)
            -- por lo tanto h solo podría ser una flecha de un objeto a sí mismo.
            conoN-law : {X Y : Obj Dos} (h : Hom Dos X Y) → (HMap F h) ∙D (conoN-ψ X) ≅ conoN-ψ Y
            conoN-law {tt} {tt} refl = idl D
            conoN-law {ff} {ff} refl = idl D
            conoN : Cone Dos D F
            conoN = cono C conoN-ψ conoN-law
        law1 : {C : Obj D} {f : HomD C A} {g : HomD C B} → proj1 ∙D ⟨ f , g ⟩ ≅ f
        law1 {C} {f} {g} = lawMorph (t conoP-t)
        law2 : {C : Obj D} {f : HomD C A} {g : HomD C B} → proj2 ∙D ⟨ f , g ⟩ ≅ g
        law2 {C} {f} {g} = lawMorph (t conoP-t)
        law3 : {C : Obj D} {f : HomD C A} {g : HomD C B} {h : HomD C (Apex conoP)} → proj1 ∙D h ≅ f → proj2 ∙D h ≅ g → h ≅ ⟨ f , g ⟩
        law3 {C} {.(proj1 ∙D h)} {.(proj2 ∙D h)} {h} refl refl =
          trans (
            sym (
              cong CHom (law conoP-t {conoN2}{cone-morph-1}))
              ) (cong CHom (law conoP-t {conoN2}{cone-morph-2}))
          where
            conoN2-ψ : (X : Obj Dos) → HomD C (OMap F X)
            conoN2-ψ tt = proj1 ∙D h  -- f
            conoN2-ψ ff = proj2 ∙D h  -- g
            conoN2-law : {X Y : Obj Dos} (h2 : Hom Dos X Y) → (HMap F h2) ∙D (conoN2-ψ X) ≅ conoN2-ψ Y
            conoN2-law {tt} {tt} refl = idl D
            conoN2-law {ff} {ff} refl = idl D
            conoN2 : Cone Dos D F
            conoN2 = cono C conoN2-ψ conoN2-law
            cone-morph-1 : ConeMorph conoN2 conoP -- chom = h
            cone-morph-1 = conoM h lawMorph-1
              where
                lawMorph-1 : {X : Obj Dos} → ψ conoP X ∙D h ≅ ψ conoN2 X
                lawMorph-1 {tt} = refl
                lawMorph-1 {ff} = refl
            cone-morph-2 : ConeMorph conoN2 conoP -- chom = fxg
            cone-morph-2 = conoM ⟨ (proj1 ∙D h) , (proj2 ∙D h)⟩ lawMorph-2
              where
                lawMorph-2 : {X : Obj Dos} → ψ conoP X ∙D ⟨ (proj1 ∙D h), (proj2 ∙D h)⟩ ≅ ψ conoN2 X
                lawMorph-2 {tt} =
                  proof          -- f x g
                    ψ conoP tt ∙D ⟨ ψ conoP tt ∙D h , ψ conoP ff ∙D h ⟩
                    ≅⟨ refl ⟩
                    ψ conoP tt ∙D CHom (t conoP-t)
                    ≅⟨ lawMorph (t conoP-t) ⟩
                    conoN2-ψ tt
                    ≅⟨ sym (idl D) ⟩
                    HMap F refl ∙D conoN2-ψ tt
                    ≅⟨ conoN2-law {Y = tt} refl ⟩
                    ψ conoN2 tt
                    ∎
                lawMorph-2 {ff} =
                  proof          -- f x g
                    ψ conoP ff ∙D ⟨ ψ conoP tt ∙D h , ψ conoP ff ∙D h ⟩
                    ≅⟨ refl ⟩
                    ψ conoP ff ∙D CHom (t conoP-t)
                    ≅⟨ lawMorph (t conoP-t) ⟩
                    conoN2-ψ ff
                    ≅⟨ sym (idl D) ⟩
                    HMap F refl ∙D conoN2-ψ ff
                    ≅⟨ conoN2-law {Y = ff} refl ⟩
                    ψ conoN2 ff
                    ∎
