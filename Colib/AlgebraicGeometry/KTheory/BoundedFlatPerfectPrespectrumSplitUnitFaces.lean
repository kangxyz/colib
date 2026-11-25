/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitUnitScalar
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassUnitTopChartJoins

/-! The original full split-unit simplex and all six exact normalization triangles.
Adapted from `OriginalUnitSquareSimplex.lean` at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. No native square evaluation is asserted. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectOriginalUnitSquareSimplex

open BoundedFlatPerfectSplitTripleSimplex (triangleFace)

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "binaryCompositeHom" => BoundedFlatPerfectBinarySimplex.composite_hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem right_first_composite :
    (rightFirstGeometric f).hom ≫ (rightFirstNormalization f).hom =
      (rightFirst f).hom := by
  have hh := congrArg (fun η ↦ whiskerLeft AsSmall.down
    (whiskerRight (eqToHom
      (congrArg boundedAboveFlatPerfectNormalizedPullback (Category.id_comp f).symm) ≫ η)
      AsSmall.up))
    (binaryCompositeHom (𝟙 X) f)
  simpa only [rightFirstGeometric, rightFirstNormalization, BoundedFlatPerfectBinarySimplex.second,
    rightFirst, boundedAboveFlatPerfectNormalizedRightUnitFirst,
    isoWhiskerLeft_hom, isoWhiskerRight_hom,
    Iso.trans_hom, eqToIso.hom, whiskerLeft_comp, whiskerRight_comp, Category.assoc] using hh

theorem right_second_composite :
    (rightSecondGeometric f).hom ≫ (rightSecondNormalization f).hom =
      (rightSecond f).hom := by
  apply NatTrans.ext
  funext A
  simp only [rightSecondGeometric, rightSecondNormalization, rightSecond,
    boundedAboveFlatPerfectNormalizedRightUnitSecond, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    Iso.trans_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    rightUnitor_hom_app]
  rw [← Functor.map_comp, ← NatTrans.comp_app, unit_composite]
  exact congrArg (fun k ↦ AsSmall.up.map k) (Category.comp_id _).symm

theorem left_first_composite :
    (leftFirstGeometric f).hom ≫ (leftFirstNormalization f).hom =
      (leftFirst f).hom := by
  have hh := congrArg (fun η ↦ whiskerLeft AsSmall.down
    (whiskerRight (eqToHom
      (congrArg boundedAboveFlatPerfectNormalizedPullback (Category.comp_id f).symm) ≫ η)
      AsSmall.up))
    (binaryCompositeHom f (𝟙 Y))
  simpa only [leftFirstGeometric, leftFirstNormalization, BoundedFlatPerfectBinarySimplex.second,
    leftFirst, boundedAboveFlatPerfectNormalizedLeftUnitFirst,
    isoWhiskerLeft_hom, isoWhiskerRight_hom,
    Iso.trans_hom, eqToIso.hom, whiskerLeft_comp, whiskerRight_comp, Category.assoc] using hh

/-- The common simplex is constructed from the original functors, not supplied as coherence. -/
def simplex : ModelSimplex (asSmallCategory (W Y))
    (asSmallCategory (W X)) 7 :=
  ModelSimplex.ofIsos (sourceMap f) (vertices f) (references f)

theorem right_first_face :
    (simplex f).face (triangleFace 0 1 2 (by decide) (by decide)) =
      ModelSimplex.triangle (F := sourceMap f) (G := rightFirstMap f) (H := rightMap f)
        (rightFirstGeometric f).hom (rightFirstNormalization f).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _
          inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact right_first_composite f

theorem right_second_face :
    (simplex f).face (triangleFace 2 3 7 (by decide) (by decide)) =
      ModelSimplex.triangle (F := rightMap f) (G := rightSecondMap f) (H := sourceMap f)
        (rightSecondGeometric f).hom (rightSecondNormalization f).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _
          inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · rfl
  · change (_ ≫ (rightSecondGeometric f).hom) ≫ (rightSecondNormalization f).hom = _
    calc
      ((rightFirst f).hom ≫ (rightSecondGeometric f).hom) ≫ (rightSecondNormalization f).hom =
          (rightFirst f).hom ≫ ((rightSecondGeometric f).hom ≫ (rightSecondNormalization f).hom) :=
        Category.assoc _ _ _
      _ = (rightFirst f).hom ≫ (rightSecond f).hom :=
        congrArg (fun k ↦ (rightFirst f).hom ≫ k) (right_second_composite f)

theorem right_normalized_face :
    (simplex f).face (triangleFace 0 2 7 (by decide) (by decide)) =
      ModelSimplex.triangle (F := sourceMap f) (G := rightMap f) (H := sourceMap f)
        (rightFirst f).hom (rightSecond f).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _
          inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · rfl

theorem left_first_face :
    (simplex f).face (triangleFace 0 4 5 (by decide) (by decide)) =
      ModelSimplex.triangle (F := sourceMap f) (G := leftFirstMap f) (H := leftMap f)
        (leftFirstGeometric f).hom (leftFirstNormalization f).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _
          inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact left_first_composite f

theorem left_second_face :
    (simplex f).face (triangleFace 5 6 7 (by decide) (by decide)) =
      ModelSimplex.triangle (F := leftMap f) (G := leftSecondMap f) (H := sourceMap f)
        (leftSecondGeometric f).hom (leftSecondNormalization f).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _
          inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · rfl
  · change (_ ≫ (leftSecondGeometric f).hom) ≫ (leftSecondNormalization f).hom = _
    rw [Category.assoc, left_second_composite]
    exact (two_routes f).symm

theorem left_normalized_face :
    (simplex f).face (triangleFace 0 5 7 (by decide) (by decide)) =
      ModelSimplex.triangle (F := sourceMap f) (G := leftMap f) (H := sourceMap f)
        (leftFirst f).hom (leftSecond f).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _
          inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact (two_routes f).symm

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectOriginalUnitSquareSimplex
