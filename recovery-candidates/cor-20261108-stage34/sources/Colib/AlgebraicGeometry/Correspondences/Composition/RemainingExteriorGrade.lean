/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.FirstTorImageCycleBaseChange
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingExteriorWeight
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Effective

/-!
# The actual dimension grade of every original exterior generic label

The third integral support has the relative dimension used by native finite 02RG.
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

local notation3 (prettyPrint := false) "C" => fieldChowSituation K
local notation3 (prettyPrint := false) "E" =>
  correspondenceLeftIntermediateSupportProduct f g h i z w v
local notation3 (prettyPrint := false) "q" => (correspondenceIncidenceMap f g h z w).toImage
local notation3 (prettyPrint := false) "π" => correspondenceLeftExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "sJ" => correspondenceIntermediateImageTarget f g h z w ≫ h
local notation3 (prettyPrint := false) "sV" =>
  (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)
local notation3 (prettyPrint := false) "sI" => q ≫ sJ
local notation3 (prettyPrint := false) "sE" => π ≫ sI

/-- The original exterior projection has the same actual third-support relative dimension. -/
theorem relativeDimension_correspondenceLeftExteriorProjection
    [LocallyOfFiniteType sV] :
    AlgebraicGeometry.RelativeDimension π
      (correspondenceThirdSupportDimension K h i v) := by
  exact AlgebraicGeometry.RelativeDimension.of_isPullback
    (IsPullback.of_hasPullback (correspondenceIncidenceRight f g h z w ≫ h) sV).flip
    (relativeDimension_of_isIntegral_over_field K sV)

/-- Native 02R8 determines the grade of each retained original exterior generic label. -/
theorem relativeDimension_correspondenceLeftExterior_generic
    [IsSeparated h] [LocallyOfFiniteType sJ] [LocallyOfFiniteType sV]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (η : genericPoints E) :
    relativeDimension (C).dimensionFunction sE η.1 =
      relativeDimension (C).dimensionFunction sI (π η.1) +
        (correspondenceThirdSupportDimension K h i v : ℤ) := by
  let := isFinite_correspondenceIncidenceToImage f g h z w hz hw
  obtain ⟨ξ, hξ⟩ := exists_correspondenceExteriorGeneric_comap f g h i z w v η
  have H := relativeDimension_comap_genericPoint_eq_add C sI sE π rfl
    (correspondenceThirdSupportDimension K h i v)
    (relativeDimension_correspondenceLeftExteriorProjection K f g h i z w v)
    (π η.1) ξ
  change relativeDimension (C).dimensionFunction sE
      (((integralComponentAt (π η.1)).comap π).subschemeι ξ.1) = _ at H
  rw [hξ] at H
  exact H

/-- The native fixed-original-label grade gives the actual closed-fibre length, with no
caller-supplied dimension comparison or reducedness assumption. -/
theorem flatPullbackWeight_correspondenceLeftExterior_originalGrade
    [IsSeparated h] [LocallyOfFiniteType sJ] [LocallyOfFiniteType sV]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (η : genericPoints E) :
    letI := isFinite_correspondenceIncidenceToImage f g h z w hz hw
    flatPullbackWeight C sE π
      (relativeDimension (C).dimensionFunction sI (π η.1) +
        (correspondenceThirdSupportDimension K h i v : ℤ)) η.1 =
      (correspondenceLeftExteriorFiberLength f g h i z w v η.1 : ℤ) := by
  let := isFinite_correspondenceIncidenceToImage f g h z w hz hw
  rw [← relativeDimension_correspondenceLeftExterior_generic K f g h i z w v hz hw η]
  exact flatPullbackWeight_correspondenceLeftExterior_generic f g h i z w v C sE η

end Stacks.Chow
