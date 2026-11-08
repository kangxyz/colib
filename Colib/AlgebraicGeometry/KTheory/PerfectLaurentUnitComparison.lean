/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarUnitComparison
public import Colib.AlgebraicGeometry.GroupScheme.LaurentOpen

/-! # The forward unit comparison on the native relative Laurent open

The schemes are the existing Stacks additive and multiplicative schemes, base-changed
along the actual map to the integral terminal scheme. Their polynomial coordinate and
forward Laurent unit are the existing native sections. No affine replacement of the base
or new scheme model is introduced.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/NativeLaurentClassComparison.lean:40-71`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the native Stacks base-change objects.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Every native perfect complex over the relative affine line has the forward unit comparison. -/
theorem perfectLaurentScalarForwardKOneClass_restrict (X : Scheme.{u})
    (K : ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := (additiveGroupBaseChange X).toRingedSpace))) :
    perfectOpenKRestrict (multiplicativeGroupBaseChangeToAdditive X) 1
        (perfectScalarForwardKOneClass (multiplicativeGroupBaseChangeToAdditive X) K
          (additiveGroupBaseChangeCoordinate X) (multiplicativeGroupBaseChangeCoordinate X)
          (multiplicativeGroupBaseChangeToAdditive_appTop_coordinate X)) =
      perfectGlobalUnitKOneClass (multiplicativeGroupBaseChange X)
        (multiplicativeGroupBaseChangeCoordinate X)
        ((perfectComplexesRestrictOpenImmersion
          (multiplicativeGroupBaseChangeToAdditive X)).obj K) :=
  perfectScalarForwardKOneClass_restrict _ _ _ _ _

/-- The native relative structure sheaf gives the forward Laurent unit, not its inverse. -/
theorem perfectLaurentScalarForwardKOneClass_restrict_rankOne (X : Scheme.{u}) :
    perfectOpenKRestrict (multiplicativeGroupBaseChangeToAdditive X) 1
        (perfectScalarForwardKOneClass (multiplicativeGroupBaseChangeToAdditive X)
          (rankOnePerfectComplex (additiveGroupBaseChange X))
          (additiveGroupBaseChangeCoordinate X) (multiplicativeGroupBaseChangeCoordinate X)
          (multiplicativeGroupBaseChangeToAdditive_appTop_coordinate X)) =
      perfectGlobalUnitKOneClass (multiplicativeGroupBaseChange X)
        (multiplicativeGroupBaseChangeCoordinate X)
        (rankOnePerfectComplex (multiplicativeGroupBaseChange X)) :=
  perfectScalarForwardKOneClass_restrict_rankOne _ _ _ _

/-- The native relative scalar cofiber retains its inverse orientation on the structure sheaf. -/
theorem perfectLaurentScalarCofiberBoundaryKOneClass_restrict_rankOne (X : Scheme.{u}) :
    perfectOpenKRestrict (multiplicativeGroupBaseChangeToAdditive X) 1
        (perfectScalarCofiberBoundaryKOneClass (multiplicativeGroupBaseChangeToAdditive X)
          (rankOnePerfectComplex (additiveGroupBaseChange X))
          (additiveGroupBaseChangeCoordinate X) (multiplicativeGroupBaseChangeCoordinate X)
          (multiplicativeGroupBaseChangeToAdditive_appTop_coordinate X)) =
      (perfectGlobalUnitKOneClass (multiplicativeGroupBaseChange X)
        (multiplicativeGroupBaseChangeCoordinate X)
        (rankOnePerfectComplex (multiplicativeGroupBaseChange X)))⁻¹ :=
  perfectScalarCofiberBoundaryKOneClass_restrict_rankOne _ _ _ _

attribute [colib_tag "COL-0305"] perfectLaurentScalarForwardKOneClass_restrict
  perfectLaurentScalarForwardKOneClass_restrict_rankOne
  perfectLaurentScalarCofiberBoundaryKOneClass_restrict_rankOne

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/NativeLaurentClassComparison.lean:40-71"
  "adaptation" "The forward polynomial coordinate on the existing native relative affine line
    restricts to its actual forward Laurent-unit class, with the original rank-one isomorphism
    and inverse cofiber orientation; no fine localization equivalence is used"]
  perfectLaurentScalarForwardKOneClass_restrict
  perfectLaurentScalarForwardKOneClass_restrict_rankOne
  perfectLaurentScalarCofiberBoundaryKOneClass_restrict_rankOne

end AlgebraicGeometry.Scheme.Modules
