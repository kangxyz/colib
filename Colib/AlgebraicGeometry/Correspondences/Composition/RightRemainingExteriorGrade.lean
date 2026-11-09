/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightFirstTorImageCycleBaseChange
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingExteriorWeight
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Effective

/-!
# The actual dimension grade of every original exterior generic label

The first integral support has the relative dimension used by native finite 02RG.
Native Stacks 02R8 computes the dimension at each generic point of the full inverse
image of an original point closure. The existing generic-label comparison supplies
that generic point, so the native flat-cycle weight is evaluated at the correct
grade without assuming a dimension equality. Ambient schemes may be disconnected
and their components may have different dimensions. Full nonreduced exterior fibre
multiplicity is retained over an arbitrary field.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The original exterior projection has the same actual first-support relative dimension. -/
theorem relativeDimension_correspondenceRightExteriorProjection
    [LocallyOfFiniteType ((((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g))] :
    let π := correspondenceRightExteriorProjection f g h i z w v
    AlgebraicGeometry.RelativeDimension π
      (correspondenceFirstSupportDimension K f g z) := by
  dsimp only
  let sV := (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)
  exact AlgebraicGeometry.RelativeDimension.of_isPullback
    (IsPullback.of_hasPullback sV (correspondenceIncidenceLeft g h i w v ≫ g))
    (relativeDimension_of_isIntegral_over_field K sV)

/-- Native 02R8 determines the grade of each retained original exterior generic label. -/
theorem relativeDimension_correspondenceRightExterior_generic
    [IsSeparated i] [LocallyOfFiniteType (((correspondenceIncidenceMap g h i w v).imageι ≫
      pullback.fst g i) ≫ g)] [LocallyOfFiniteType ((((integralComponentAt z).subschemeι ≫
      pullback.snd f g) ≫ g))]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (η : genericPoints (correspondenceRightIntermediateSupportProduct f g h i z w v)) :
    let C := fieldChowSituation K
    let q := (correspondenceIncidenceMap g h i w v).toImage
    let π := correspondenceRightExteriorProjection f g h i z w v
    let sJ := ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g
    let sI := q ≫ sJ
    let sE := π ≫ sI
    relativeDimension (C).dimensionFunction sE η.1 =
      relativeDimension (C).dimensionFunction sI (π η.1) +
        (correspondenceFirstSupportDimension K f g z : ℤ) := by
  dsimp only
  let C := fieldChowSituation K
  let q := (correspondenceIncidenceMap g h i w v).toImage
  let π := correspondenceRightExteriorProjection f g h i z w v
  let sJ := ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g
  let sI := q ≫ sJ
  let sE := π ≫ sI
  let := isFinite_correspondenceIncidenceToImage g h i w v hw hv
  obtain ⟨ξ, hξ⟩ := exists_correspondenceRightExteriorGeneric_comap f g h i z w v η
  have H := relativeDimension_comap_genericPoint_eq_add C sI sE π rfl
    (correspondenceFirstSupportDimension K f g z)
    (relativeDimension_correspondenceRightExteriorProjection K f g h i z w v)
    (π η.1) ξ
  change relativeDimension (C).dimensionFunction sE
      (((integralComponentAt (π η.1)).comap π).subschemeι ξ.1) = _ at H
  rw [hξ] at H
  exact H

/-- The native fixed-original-label grade gives the actual closed-fibre length, with no
caller-supplied dimension comparison or reducedness assumption. -/
theorem flatPullbackWeight_correspondenceRightExterior_originalGrade
    [IsSeparated i] [LocallyOfFiniteType (((correspondenceIncidenceMap g h i w v).imageι ≫
      pullback.fst g i) ≫ g)] [LocallyOfFiniteType ((((integralComponentAt z).subschemeι ≫
      pullback.snd f g) ≫ g))]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (η : genericPoints (correspondenceRightIntermediateSupportProduct f g h i z w v)) :
    let C := fieldChowSituation K
    let q := (correspondenceIncidenceMap g h i w v).toImage
    let π := correspondenceRightExteriorProjection f g h i z w v
    let sJ := ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g
    let sI := q ≫ sJ
    let sE := π ≫ sI
    letI := isFinite_correspondenceIncidenceToImage g h i w v hw hv
    flatPullbackWeight C sE π
      (relativeDimension (C).dimensionFunction sI (π η.1) +
        (correspondenceFirstSupportDimension K f g z : ℤ)) η.1 =
      (correspondenceRightExteriorFiberLength f g h i z w v η.1 : ℤ) := by
  dsimp only
  let C := fieldChowSituation K
  let q := (correspondenceIncidenceMap g h i w v).toImage
  let π := correspondenceRightExteriorProjection f g h i z w v
  let sJ := ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g
  let sI := q ≫ sJ
  let sE := π ≫ sI
  let := isFinite_correspondenceIncidenceToImage g h i w v hw hv
  rw [← relativeDimension_correspondenceRightExterior_generic K f g h i z w v hw hv η]
  exact flatPullbackWeight_correspondenceRightExterior_generic f g h i z w v C sE η

end Stacks.Chow
