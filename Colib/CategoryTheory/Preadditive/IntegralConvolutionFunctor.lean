/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Preadditive.IntegralConvolutionPresheaf
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence

/-!
# Biadditivity of the integral tensor coend

Coefficient maps act on the two literal pure-tensor factors. This makes
the coend a biadditive functor on transfer presheaves, which is the input
required by the signed projective derived construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory TensorProduct

universe u v w

namespace CategoryTheory.Preadditive.Convolution

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (F : C ⥤ C ⥤ C)

/-- Maps of convolution presheaves are determined by the pure generators. -/
theorem presheaf_hom_ext {P Q R : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})}
    {f g : presheaf F P.obj Q.obj ⟶ R}
    (h : ∀ (X Y Z : C) (s : (P.obj.obj (op Y))) (t : (Q.obj.obj (op Z)))
      (a : X ⟶ (F.obj Y).obj Z),
      f.hom.app (op X) (generator F P.obj Q.obj X Y Z s t a) =
        g.hom.app (op X) (generator F P.obj Q.obj X Y Z s t a)) : f = g := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  let U := forget₂ (ModuleCat.{max u v w} ℤ) AddCommGrpCat.{max u v w}
  let M := sections F P.obj Q.obj X.unop
  let N := ModuleCat.of ℤ ((R.obj.obj (op X.unop)))
  let φ : U.obj M ⟶ U.obj N := f.hom.app X
  let ψ : U.obj M ⟶ U.obj N := g.hom.app X
  have hfg : U.preimage φ = U.preimage ψ := by
    apply sections_hom_ext
    intro Y Z s t a
    let z := generator F P.obj Q.obj X.unop Y Z s t a
    exact (ConcreteCategory.congr_hom (U.map_preimage φ) z).trans
      ((h X.unop Y Z s t a).trans (ConcreteCategory.congr_hom (U.map_preimage ψ) z).symm)
  change φ = ψ
  rw [← U.map_preimage φ, ← U.map_preimage ψ, hfg]

variable {P P' P'' Q Q' Q'' : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})}

/-- Apply the two coefficient maps in the external tensor. -/
def coefficientMap (f : P ⟶ P') (g : Q ⟶ Q') :
    coefficientModule P.obj Q.obj ⟶ coefficientModule P'.obj Q'.obj :=
  Functor.whiskerLeft (prodOpEquiv (D := C) (C)).functor
    (Functor.whiskerRight
      (NatTrans.prod (Functor.whiskerRight f.hom integerModuleFunctor)
        (Functor.whiskerRight g.hom integerModuleFunctor))
        (MonoidalCategory.tensor (ModuleCat.{max u v w} ℤ)))

/-- The map of coend diagrams induced by the actual coefficient maps. -/
def mapDiagram (f : P ⟶ P') (g : Q ⟶ Q') (X : C) :
    diagram F P.obj Q.obj X ⟶ diagram F P'.obj Q'.obj X :=
  Functor.curry.map (Functor.whiskerRight
    (NatTrans.prod (coefficientMap f g) (𝟙 (homModule F X)))
    (MonoidalCategory.tensor (ModuleCat.{max u v w} ℤ)))

/-- The induced map of the original coend modules. -/
def mapApp (f : P ⟶ P') (g : Q ⟶ Q') (X : C) :
    sections F P.obj Q.obj X ⟶ sections F P'.obj Q'.obj X :=
  coend.map (mapDiagram F f g X)

@[simp]
theorem mapApp_generator (f : P ⟶ P') (g : Q ⟶ Q')
    (X Y Z : C) (s : (P.obj.obj (op Y))) (t : (Q.obj.obj (op Z))) (a : X ⟶ (F.obj Y).obj Z) :
    mapApp F f g X (generator F P.obj Q.obj X Y Z s t a) =
      generator F P'.obj Q'.obj X Y Z (f.hom.app (op Y) s) (g.hom.app (op Z) t) a :=
  ConcreteCategory.congr_hom (coend.ι_map (mapDiagram F f g X) (Y, Z))
    (show ((diagram F P.obj Q.obj X).obj (op (Y, Z))).obj (Y, Z) from
      (s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a)

/-- The coend coefficient map commutes with every original transfer. -/
def map (f : P ⟶ P') (g : Q ⟶ Q') :
    presheaf F P.obj Q.obj ⟶ presheaf F P'.obj Q'.obj :=
  ObjectProperty.homMk
    { app X :=
  (forget₂ (ModuleCat.{max u v w} ℤ) AddCommGrpCat.{max u v w}).map (mapApp F f g X.unop)
      naturality X X' β := by
        let U := forget₂ (ModuleCat.{max u v w} ℤ) AddCommGrpCat.{max u v w}
        change U.map (transfer F P.obj Q.obj β.unop) ≫
            U.map (mapApp F f g X'.unop) =
          U.map (mapApp F f g X.unop) ≫
            U.map (transfer F P'.obj Q'.obj β.unop)
        rw [← U.map_comp, ← U.map_comp]
        apply congrArg U.map
        apply sections_hom_ext
        intro Y Z s t a
        simp only [ModuleCat.comp_apply, transfer_generator,
          mapApp_generator] }

@[simp]
theorem map_generator (f : P ⟶ P') (g : Q ⟶ Q')
    (X Y Z : C) (s : (P.obj.obj (op Y))) (t : (Q.obj.obj (op Z))) (a : X ⟶ (F.obj Y).obj Z) :
    (map F f g).hom.app (op X) (generator F P.obj Q.obj X Y Z s t a) =
      generator F P'.obj Q'.obj X Y Z (f.hom.app (op Y) s) (g.hom.app (op Z) t) a :=
  mapApp_generator F f g X Y Z s t a

@[simp]
theorem map_id (P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) : map F (𝟙 P) (𝟙 Q)
    = 𝟙 _ := by
  apply presheaf_hom_ext
  intro X Y Z s t a
  rw [map_generator]
  rfl

@[reassoc]
theorem map_comp (f : P ⟶ P') (f' : P' ⟶ P'')
    (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    map F (f ≫ f') (g ≫ g') =
      map F f g ≫ map F f' g' := by
  apply presheaf_hom_ext
  intro X Y Z s t a
  change (map F (f ≫ f') (g ≫ g')).hom.app (op X)
      (generator F P.obj Q.obj X Y Z s t a) =
    (map F f' g').hom.app (op X)
      ((map F f g).hom.app (op X) (generator F P.obj Q.obj X Y Z s t a))
  rw [map_generator, map_generator, map_generator]
  rfl

/-- The native coend, functorial in the pair of coefficient presheaves. -/
def functor : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) × (Cᵒᵖ ⥤+
    AddCommGrpCat.{max u v w}) ⥤ (Cᵒᵖ
    ⥤+ AddCommGrpCat.{max u v w}) where
  obj PQ := presheaf F PQ.1.obj PQ.2.obj
  map f := map F f.1 f.2
  map_id PQ := map_id F PQ.1 PQ.2
  map_comp f g := map_comp F f.1 g.1 f.2 g.2

/-- The curried integral tensor coend. -/
def bifunctor : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) ⥤ (Cᵒᵖ ⥤+
    AddCommGrpCat.{max u v w}) ⥤ (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) :=
  Functor.curry.obj (functor F)

instance (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) : ((bifunctor F).obj P).Additive where
  map_add {Q Q' f g} := by
    apply presheaf_hom_ext
    intro X Y Z s t a
    change (map F (𝟙 P) (f + g)).hom.app (op X)
        (generator F P.obj Q.obj X Y Z s t a) =
      (map F (𝟙 P) f).hom.app (op X)
        (generator F P.obj Q.obj X Y Z s t a) +
      (map F (𝟙 P) g).hom.app (op X)
        (generator F P.obj Q.obj X Y Z s t a)
    rw [map_generator, map_generator, map_generator]
    exact generator_add_right F P.obj Q'.obj s (f.hom.app (op Z) t)
      (g.hom.app (op Z) t) a

instance : (bifunctor F).Additive where
  map_add {P P' f g} := by
    apply NatTrans.ext
    funext Q
    apply presheaf_hom_ext
    intro X Y Z s t a
    change (map F (f + g) (𝟙 Q)).hom.app (op X)
        (generator F P.obj Q.obj X Y Z s t a) =
      (map F f (𝟙 Q)).hom.app (op X)
        (generator F P.obj Q.obj X Y Z s t a) +
      (map F g (𝟙 Q)).hom.app (op X)
        (generator F P.obj Q.obj X Y Z s t a)
    rw [map_generator, map_generator, map_generator]
    exact generator_add_left F P'.obj Q.obj (f.hom.app (op Y) s)
      (g.hom.app (op Y) s) t a

end CategoryTheory.Preadditive.Convolution
