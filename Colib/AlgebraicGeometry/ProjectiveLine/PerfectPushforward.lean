/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.FlatAndRelativeDimension
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceNoetherian.Basic

/-! # Perfect direct images along the projective-line projection

The actual bounded-below derived direct image preserves intrinsic perfection.
There is no hypothesis of affineness or quasi-compactness on the base.

* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.projectiveSpaceOver

attribute [local instance] HasDerivedCategory.standard

/-- The actual derived direct image along the projective line preserves perfect objects. -/
theorem isPerfect_projectiveLineDerivedPushforwardPlus (S : Scheme.{u})
    (K : DerivedCategory.Plus (projectiveSpaceOver 1 S).Modules)
    (hK : RingedSpace.IsPerfect (X := (projectiveSpaceOver 1 S).toRingedSpace)
      (DerivedCategory.Plus.ι.obj K)) :
    RingedSpace.IsPerfect (X := S.toRingedSpace)
      (DerivedCategory.Plus.ι.obj
        ((Scheme.Modules.pushforward (projectiveSpaceOver 1 S ↘ S)).rightDerivedFunctorPlus.obj
          K)) := by
  let f := projectiveSpaceOver 1 S ↘ S
  have := locallyOfFiniteType_terminal_from_projectiveSpaceAtUniverse.{u} 1
  let : LocallyOfFinitePresentation f := by
    change LocallyOfFinitePresentation (pullback.fst _ _)
    infer_instance
  have h : RingedSpace.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj K.obj) :=
    isPerfect_derivedPushforward_of_flat_of_isProper f K.obj hK
  obtain ⟨a, ha⟩ := K.property
  obtain ⟨e⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    (Scheme.Modules.pushforward f) (derivedPushforwardModules f)
    (derivedPushforwardModulesUnit f)
    (fun I hI => RingedSpace.isIso_derivedPushforwardUnit_app_of_isKInjective _ I hI) K a ha
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    (X := S.toRingedSpace) e h

end AlgebraicGeometry.projectiveSpaceOver
