/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.Convolution
public import Colib.CategoryTheory.Preadditive.IntegralConvolutionFunctor
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

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "MZ(" K ")" => IntegerCoefficients K

local notation "PST(" K ")" => TransferCoefficients K

variable (F : Cor k ⥤ Cor k ⥤ Cor k)

/-- Maps of convolution presheaves are determined by the pure generators. -/
theorem convolutionPresheaf_hom_ext {P Q R : PST(k)}
    {f g : convolutionPresheaf F P Q ⟶ R}
    (h : ∀ (X Y Z : Cor k) (s : sections P Y) (t : sections Q Z)
      (a : X ⟶ (F.obj Y).obj Z),
      f.hom.app (op X) (convolutionGenerator F P Q X Y Z s t a) =
        g.hom.app (op X) (convolutionGenerator F P Q X Y Z s t a)) : f = g := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  let U := forget₂ MZ(k) AddCommGrpCat.{u + 1}
  let M := convolutionSections F P Q X.unop
  let N := ModuleCat.of ℤ (sections R X.unop)
  let φ : U.obj M ⟶ U.obj N := f.hom.app X
  let ψ : U.obj M ⟶ U.obj N := g.hom.app X
  have hfg : U.preimage φ = U.preimage ψ := by
    apply convolutionSections_hom_ext
    intro Y Z s t a
    let z := convolutionGenerator F P Q X.unop Y Z s t a
    exact (ConcreteCategory.congr_hom (U.map_preimage φ) z).trans
      ((h X.unop Y Z s t a).trans (ConcreteCategory.congr_hom (U.map_preimage ψ) z).symm)
  change φ = ψ
  rw [← U.map_preimage φ, ← U.map_preimage ψ, hfg]

variable {P P' P'' Q Q' Q'' : PST(k)}

/-- Apply the two coefficient maps in the external tensor. -/
def convolutionCoefficientMap (f : P ⟶ P') (g : Q ⟶ Q') :
    convolutionCoefficientModule P Q ⟶ convolutionCoefficientModule P' Q' :=
  CategoryTheory.Preadditive.Convolution.coefficientMap.{u + 1, u, 0} f g

/-- The map of coend diagrams induced by the actual coefficient maps. -/
def convolutionMapDiagram (f : P ⟶ P') (g : Q ⟶ Q') (X : Cor k) :
    convolutionDiagram F P Q X ⟶ convolutionDiagram F P' Q' X :=
  CategoryTheory.Preadditive.Convolution.mapDiagram.{u + 1, u, 0} F f g X

/-- The induced map of the original coend modules. -/
def convolutionMapApp (f : P ⟶ P') (g : Q ⟶ Q') (X : Cor k) :
    convolutionSections F P Q X ⟶ convolutionSections F P' Q' X :=
  coend.map (convolutionMapDiagram F f g X)

@[simp]
theorem convolutionMapApp_generator (f : P ⟶ P') (g : Q ⟶ Q')
    (X Y Z : Cor k) (s : sections P Y) (t : sections Q Z) (a : X ⟶ (F.obj Y).obj Z) :
    convolutionMapApp F f g X (convolutionGenerator F P Q X Y Z s t a) =
      convolutionGenerator F P' Q' X Y Z (f.hom.app (op Y) s) (g.hom.app (op Z) t) a :=
  ConcreteCategory.congr_hom (coend.ι_map (convolutionMapDiagram F f g X) (Y, Z))
    (show ((convolutionDiagram F P Q X).obj (op (Y, Z))).obj (Y, Z) from
      (s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a)

/-- The coend coefficient map commutes with every original transfer. -/
def convolutionMap (f : P ⟶ P') (g : Q ⟶ Q') :
    convolutionPresheaf F P Q ⟶ convolutionPresheaf F P' Q' :=
  ObjectProperty.homMk
    { app X := (forget₂ MZ(k) AddCommGrpCat.{u + 1}).map (convolutionMapApp F f g X.unop)
      naturality X X' β := by
        let U := forget₂ MZ(k) AddCommGrpCat.{u + 1}
        change U.map (convolutionTransfer F P Q β.unop) ≫
            U.map (convolutionMapApp F f g X'.unop) =
          U.map (convolutionMapApp F f g X.unop) ≫
            U.map (convolutionTransfer F P' Q' β.unop)
        rw [← U.map_comp, ← U.map_comp]
        apply congrArg U.map
        apply convolutionSections_hom_ext
        intro Y Z s t a
        simp only [ModuleCat.comp_apply, convolutionTransfer_generator,
          convolutionMapApp_generator] }

@[simp]
theorem convolutionMap_generator (f : P ⟶ P') (g : Q ⟶ Q')
    (X Y Z : Cor k) (s : sections P Y) (t : sections Q Z) (a : X ⟶ (F.obj Y).obj Z) :
    (convolutionMap F f g).hom.app (op X) (convolutionGenerator F P Q X Y Z s t a) =
      convolutionGenerator F P' Q' X Y Z (f.hom.app (op Y) s) (g.hom.app (op Z) t) a :=
  convolutionMapApp_generator F f g X Y Z s t a

@[simp]
theorem convolutionMap_id (P Q : PST(k)) : convolutionMap F (𝟙 P) (𝟙 Q) = 𝟙 _ := by
  apply convolutionPresheaf_hom_ext
  intro X Y Z s t a
  rw [convolutionMap_generator]
  rfl

@[reassoc]
theorem convolutionMap_comp (f : P ⟶ P') (f' : P' ⟶ P'')
    (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    convolutionMap F (f ≫ f') (g ≫ g') =
      convolutionMap F f g ≫ convolutionMap F f' g' := by
  apply convolutionPresheaf_hom_ext
  intro X Y Z s t a
  change (convolutionMap F (f ≫ f') (g ≫ g')).hom.app (op X)
      (convolutionGenerator F P Q X Y Z s t a) =
    (convolutionMap F f' g').hom.app (op X)
      ((convolutionMap F f g).hom.app (op X) (convolutionGenerator F P Q X Y Z s t a))
  rw [convolutionMap_generator, convolutionMap_generator, convolutionMap_generator]
  rfl

/-- The native coend, functorial in the pair of coefficient presheaves. -/
def convolutionFunctor : PST(k) × PST(k) ⥤ PST(k) where
  obj PQ := convolutionPresheaf F PQ.1 PQ.2
  map f := convolutionMap F f.1 f.2
  map_id PQ := convolutionMap_id F PQ.1 PQ.2
  map_comp f g := convolutionMap_comp F f.1 g.1 f.2 g.2

/-- The curried integral tensor coend. -/
def convolutionBifunctor : PST(k) ⥤ PST(k) ⥤ PST(k) := Functor.curry.obj (convolutionFunctor F)

instance (P : PST(k)) : ((convolutionBifunctor F).obj P).Additive where
  map_add {Q Q' f g} := by
    apply convolutionPresheaf_hom_ext
    intro X Y Z s t a
    change (convolutionMap F (𝟙 P) (f + g)).hom.app (op X)
        (convolutionGenerator F P Q X Y Z s t a) =
      (convolutionMap F (𝟙 P) f).hom.app (op X)
        (convolutionGenerator F P Q X Y Z s t a) +
      (convolutionMap F (𝟙 P) g).hom.app (op X)
        (convolutionGenerator F P Q X Y Z s t a)
    rw [convolutionMap_generator, convolutionMap_generator, convolutionMap_generator]
    exact convolutionGenerator_add_right F P Q' s (f.hom.app (op Z) t)
      (g.hom.app (op Z) t) a

instance : (convolutionBifunctor F).Additive where
  map_add {P P' f g} := by
    apply NatTrans.ext
    funext Q
    apply convolutionPresheaf_hom_ext
    intro X Y Z s t a
    change (convolutionMap F (f + g) (𝟙 Q)).hom.app (op X)
        (convolutionGenerator F P Q X Y Z s t a) =
      (convolutionMap F f (𝟙 Q)).hom.app (op X)
        (convolutionGenerator F P Q X Y Z s t a) +
      (convolutionMap F g (𝟙 Q)).hom.app (op X)
        (convolutionGenerator F P Q X Y Z s t a)
    rw [convolutionMap_generator, convolutionMap_generator, convolutionMap_generator]
    exact convolutionGenerator_add_left F P' Q (f.hom.app (op Y) s)
      (g.hom.app (op Y) s) t a

end AlgebraicGeometry.PresheafWithTransfers
