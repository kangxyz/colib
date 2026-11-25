/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumIdentitySimplex
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectProjectionBinaryRows
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectReferenceCoherence
import Mathlib.Tactic.FinCases

/-! The original eight split unit reference nodes, and both original first binary rows.
Adapted from `OriginalUnitSquareSimplex.lean` and `CoefficientBassUnitHZeroNodes.lean`
at Quillen `c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectOriginalUnitSquareSimplex

open BoundedFlatPerfectReferenceCoherence

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "binaryGeometricIso" => BoundedFlatPerfectBinarySimplex.geometricIso
local notation "binaryMidMap" => BoundedFlatPerfectBinarySimplex.intermediateMap
local notation "binarySecond" => BoundedFlatPerfectBinarySimplex.second
local notation "binarySourceMap" => BoundedFlatPerfectBinarySimplex.sourceMap
local notation "binaryTargetMap" => BoundedFlatPerfectBinarySimplex.targetMap
local notation "N" => boundedAboveFlatPerfectNormalizedPullback

/-- The genuine normalization intermediate of the original identity track. -/
def unitIntermediate (X : Scheme.{u}) :
    (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory ⥤
      (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory :=
  CategoryTheory.rebaseFunctor (𝟭 (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory)
    (W X).zero (W X).zero
    (((IsExact.id (W X).cof
      (W X).weq).zero (W X).isZero).iso
      (W X).isZero)

/-- The geometric comparison from identity pullback to its rebased intermediate. -/
def unitGeometric (X : Scheme.{u}) :
    boundedAboveFlatPerfectNormalizedPullback (𝟙 X) ≅ unitIntermediate X :=
  (boundedAboveFlatPerfectPullbackNormalizationIso (𝟙 X)).symm ≪≫
    boundedAboveFlatPerfectPullbackIdIso X ≪≫ CategoryTheory.rebaseFunctorIso _ _ _ _

/-- The normalization from the rebased identity functor to the identity functor. -/
def unitNormalization (X : Scheme.{u}) :
    unitIntermediate X ≅ 𝟭 (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory :=
  (CategoryTheory.rebaseFunctorIso _ _ _ _).symm

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The model map induced by normalized pullback along the original scheme map. -/
abbrev sourceMap := BoundedFlatPerfectProjectionBinaryRows.normalizedMap f

/-- The target model map of the original right-unit binary normalization. -/
abbrev rightMap := binaryTargetMap (𝟙 X) f
/-- The target model map of the original left-unit binary normalization. -/
abbrev leftMap := binaryTargetMap f (𝟙 Y)
/-- The intermediate model map of the first right-unit comparison. -/
abbrev rightFirstMap := binaryMidMap (𝟙 X) f
/-- The intermediate model map of the first left-unit comparison. -/
abbrev leftFirstMap := binaryMidMap f (𝟙 Y)

/-- The model map with the rebased identity after the original pullback. -/
def rightSecondMap : asSmallCategory (W Y) ⟶
    asSmallCategory (W X) :=
  asSmallCategoryMap (W Y) (W X) ((boundedAboveFlatPerfectNormalizedPullback_exact f).comp
    (IsExact.id (W X).cof
      (W X).weq).rebase)
    (by simp only [comp_obj, boundedAboveFlatPerfectNormalizedPullback_obj_zero,
      CategoryTheory.rebaseFunctor_obj_base])

/-- The model map with the rebased identity before the original pullback. -/
def leftSecondMap : asSmallCategory (W Y) ⟶
    asSmallCategory (W X) :=
  asSmallCategoryMap (W Y) (W X) ((IsExact.id (W Y).cof
    (W Y).weq).rebase.comp (boundedAboveFlatPerfectNormalizedPullback_exact f))
    (by simp only [comp_obj, CategoryTheory.rebaseFunctor_obj_base,
      boundedAboveFlatPerfectNormalizedPullback_obj_zero])

/-- The first unsplit right-unit comparison from the original source map. -/
def rightFirst : (sourceMap f).hom.toFunctor ≅ (rightMap f).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (boundedAboveFlatPerfectNormalizedRightUnitFirst f) AsSmall.up)

/-- The second unsplit right-unit comparison back to the original source map. -/
def rightSecond : (rightMap f).hom.toFunctor ≅ (sourceMap f).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (boundedAboveFlatPerfectNormalizedRightUnitSecond f) AsSmall.up)

/-- The geometric component of the first right-unit comparison. -/
def rightFirstGeometric : (sourceMap f).hom.toFunctor ≅ (rightFirstMap f).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback (Category.id_comp f).symm) ≪≫
      binaryGeometricIso (𝟙 X) f) AsSmall.up)

/-- The normalization component of the first right-unit comparison. -/
abbrev rightFirstNormalization := binarySecond (𝟙 X) f

/-- The geometric component of the second right-unit comparison. -/
def rightSecondGeometric : (rightMap f).hom.toFunctor ≅ (rightSecondMap f).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (isoWhiskerLeft (boundedAboveFlatPerfectNormalizedPullback f) (unitGeometric X)) AsSmall.up)

/-- The normalization component of the second right-unit comparison. -/
def rightSecondNormalization : (rightSecondMap f).hom.toFunctor ≅ (sourceMap f).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (isoWhiskerLeft (boundedAboveFlatPerfectNormalizedPullback f) (unitNormalization X)) AsSmall.up)

/-- The first unsplit left-unit comparison from the original source map. -/
def leftFirst : (sourceMap f).hom.toFunctor ≅ (leftMap f).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (boundedAboveFlatPerfectNormalizedLeftUnitFirst f) AsSmall.up)

/-- The second unsplit left-unit comparison back to the original source map. -/
def leftSecond : (leftMap f).hom.toFunctor ≅ (sourceMap f).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (boundedAboveFlatPerfectNormalizedLeftUnitSecond f) AsSmall.up)

/-- The geometric component of the first left-unit comparison. -/
def leftFirstGeometric : (sourceMap f).hom.toFunctor ≅ (leftFirstMap f).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback (Category.comp_id f).symm) ≪≫
      binaryGeometricIso f (𝟙 Y)) AsSmall.up)

/-- The normalization component of the first left-unit comparison. -/
abbrev leftFirstNormalization := binarySecond f (𝟙 Y)

/-- The geometric component of the second left-unit comparison. -/
def leftSecondGeometric : (leftMap f).hom.toFunctor ≅ (leftSecondMap f).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (isoWhiskerRight (unitGeometric Y) (boundedAboveFlatPerfectNormalizedPullback f)) AsSmall.up)

/-- The normalization component of the second left-unit comparison. -/
def leftSecondNormalization : (leftSecondMap f).hom.toFunctor ≅ (sourceMap f).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (isoWhiskerRight (unitNormalization Y) (boundedAboveFlatPerfectNormalizedPullback f))
    AsSmall.up)

/-- Eight actual functors, including both split identity normalization intermediates. -/
def vertices : Fin 8 → (asSmallCategory (W Y) ⟶
    asSmallCategory (W X)) :=
  ![sourceMap f, rightFirstMap f, rightMap f, rightSecondMap f,
    leftFirstMap f, leftMap f, leftSecondMap f, sourceMap f]

/-- The original source-reference isomorphisms for all eight unit-square vertices. -/
def references : ∀ i, (sourceMap f).hom.toFunctor ≅ (vertices f i).hom.toFunctor :=
  Fin.cases (Iso.refl _) (Fin.cases (rightFirstGeometric f)
    (Fin.cases (rightFirst f) (Fin.cases (rightFirst f ≪≫ rightSecondGeometric f)
      (Fin.cases (leftFirstGeometric f) (Fin.cases (leftFirst f)
        (Fin.cases (leftFirst f ≪≫ leftSecondGeometric f)
          (Fin.cases (rightFirst f ≪≫ rightSecond f) (fun i ↦ Fin.elim0 i))))))))

/-- Actual scheme-unit transport into the first old binary comparison. -/
theorem rightBinarySourceEq : (sourceMap f).hom.toFunctor =
    (binarySourceMap (𝟙 X) f).hom.toFunctor :=
  congrArg (fun G ↦ AsSmall.down ⋙ G ⋙ AsSmall.up)
    (congrArg boundedAboveFlatPerfectNormalizedPullback (Category.id_comp f).symm)

/-- Actual scheme-unit transport into the other old binary comparison. -/
theorem leftBinarySourceEq : (sourceMap f).hom.toFunctor =
    (binarySourceMap f (𝟙 Y)).hom.toFunctor :=
  congrArg (fun G ↦ AsSmall.down ⋙ G ⋙ AsSmall.up)
    (congrArg boundedAboveFlatPerfectNormalizedPullback (Category.comp_id f).symm)

/-- The original first binary row, including its geometric normalization intermediate. -/
theorem unit_right_row (i : Fin 3) :
    (⟨vertices f (![0, 1, 2] i), references f (![0, 1, 2] i)⟩ :
      Σ G : asSmallCategory (W Y) ⟶
        asSmallCategory (W X), (sourceMap f).hom.toFunctor ≅ G.hom.toFunctor) =
      ModelSimplex.reanchorNode (eqToIso (rightBinarySourceEq f))
        (BoundedFlatPerfectProjectionBinaryRows.binaryNodes (𝟙 X) f i) := by
  fin_cases i
  · apply ModelSimplex.reference_node_eq (rightBinarySourceEq f)
    simp [references, BoundedFlatPerfectProjectionBinaryRows.binaryNodes]
  · apply ModelSimplex.reference_node_eq rfl
    simp only [eqToHom_refl, Category.comp_id]
    exact congrArg Iso.hom ((smallIso_trans (eqToIso (congrArg N (Category.id_comp f).symm))
      (binaryGeometricIso (𝟙 X) f)).trans
      (congrArg (fun η ↦ η ≪≫ smallIso (binaryGeometricIso (𝟙 X) f))
        (smallIso_eqToIso (congrArg N (Category.id_comp f).symm))))
  · apply ModelSimplex.reference_node_eq rfl
    simp only [eqToHom_refl, Category.comp_id]
    exact congrArg Iso.hom ((smallIso_trans (eqToIso (congrArg N (Category.id_comp f).symm))
      (boundedAboveFlatPerfectNormalizedPullbackCompIso (𝟙 X) f)).trans
      (congrArg (fun η ↦ η ≪≫ smallIso (boundedAboveFlatPerfectNormalizedPullbackCompIso (𝟙 X) f))
        (smallIso_eqToIso (congrArg N (Category.id_comp f).symm))))

/-- The second binary row keeps the other exact scheme-unit transport. -/
theorem unit_left_row (i : Fin 3) :
    (⟨vertices f (![0, 4, 5] i), references f (![0, 4, 5] i)⟩ :
      Σ G : asSmallCategory (W Y) ⟶
        asSmallCategory (W X), (sourceMap f).hom.toFunctor ≅ G.hom.toFunctor) =
      ModelSimplex.reanchorNode (eqToIso (leftBinarySourceEq f))
        (BoundedFlatPerfectProjectionBinaryRows.binaryNodes f (𝟙 Y) i) := by
  fin_cases i
  · apply ModelSimplex.reference_node_eq (leftBinarySourceEq f)
    simp [references, BoundedFlatPerfectProjectionBinaryRows.binaryNodes]
  · apply ModelSimplex.reference_node_eq rfl
    simp only [eqToHom_refl, Category.comp_id]
    exact congrArg Iso.hom ((smallIso_trans (eqToIso (congrArg N (Category.comp_id f).symm))
      (binaryGeometricIso f (𝟙 Y))).trans
      (congrArg (fun η ↦ η ≪≫ smallIso (binaryGeometricIso f (𝟙 Y)))
        (smallIso_eqToIso (congrArg N (Category.comp_id f).symm))))
  · apply ModelSimplex.reference_node_eq rfl
    simp only [eqToHom_refl, Category.comp_id]
    exact congrArg Iso.hom ((smallIso_trans (eqToIso (congrArg N (Category.comp_id f).symm))
      (boundedAboveFlatPerfectNormalizedPullbackCompIso f (𝟙 Y))).trans
      (congrArg (fun η ↦ η ≪≫ smallIso (boundedAboveFlatPerfectNormalizedPullbackCompIso f (𝟙 Y)))
        (smallIso_eqToIso (congrArg N (Category.comp_id f).symm))))
end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectOriginalUnitSquareSimplex
