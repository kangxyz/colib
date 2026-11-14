/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.DerivedCechTriangle
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PerfectGlobalSectionsAffineBase
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.FlatAndRelativeDimension
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceNoetherian.Basic

/-! # Perfect derived sections of a projective-line vector bundle

Over any commutative ring, the derived global sections of a finite locally free
sheaf on the projective line are perfect. This is the proper, flat direct-image
theorem, not a Noetherian finiteness argument.

## References

* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)

universe u

namespace AlgebraicGeometry.projectiveSpaceOver

attribute [local instance] HasDerivedCategory.standard

/-- Derived sections of a vector bundle on the projective line over an arbitrary ring are
perfect over the base ring. -/
theorem isPerfect_lineDerivedSections (R : CommRingCat.{u}) (M : (line R).Modules)
    [M.IsQuasicoherent] [SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    StacksDraft.Perfect.IsPerfect (derivedGlobalSectionsOverBase (lineProjection R) M) := by
  have := locallyOfFiniteType_terminal_from_projectiveSpaceAtUniverse.{u} 1
  let : LocallyOfFinitePresentation (lineProjection R) := by
    change LocallyOfFinitePresentation (CategoryTheory.Limits.pullback.fst _ _)
    infer_instance
  let f := lineProjection R
  have hf : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  have h := ProperFlatBaseChange.isPerfect_derivedPushforward_module f hf inferInstance M
    (Stacks.FiniteLocallyFree.isFinitePresentation M)
    (VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree f M)
  apply isPerfect_derivedGlobalSectionsOverBase_of_isPerfect_derivedPushforward
  exact isPerfect_of_iso_scheme
    ((derivedPushforward f.toLRSHom.toShHom).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (line R).Modules 0).app M)) h

end AlgebraicGeometry.projectiveSpaceOver
