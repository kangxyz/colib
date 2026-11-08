/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectGlobalUnitKOne
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberKOneNormalization

/-! # Actual restriction of the independent forward scalar K-one class

The coarse scalar class is not defined through its restriction. The existing naturality
of the actual weak-arrow class proves its image is the independently defined fine unit class.
The cofiber boundary retains its inverse orientation, before the separate relative
connecting-map formula. No equivalence between coarse and fine-open K-theory is asserted.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarLaurentClassComparison.lean:49-83`
and `GlobalUnitKOneInversion.lean:41-48` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory Waldhausen

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- Canonical coarse restriction sends the independent forward scalar to the actual fine unit. -/
theorem perfectScalarForwardKOneClass_restrict :
    perfectOpenKRestrict j 1 (perfectScalarForwardKOneClass j K r q hq) =
      perfectGlobalUnitKOneClass U q ((perfectComplexesRestrictOpenImmersion j).obj K) := by
  exact (KMap_weakEndomorphismKOneClass (V := perfectOpenWeakWaldhausen j)
    (W := RingedSpace.perfectComplexesWaldhausen U.toRingedSpace) (perfectOpenRestrict_isExact j)
    ((perfectGlobalScalar X r).app K)
    (quasiIso_restrict_complexGlobalScalar j r q hq K.obj)).trans
      ((RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).weakEndomorphismKOneClass_congr
        (perfectRestrict_scalar_eq_globalUnit j r q hq K) _ _)

/-- The actual cofiber boundary still restricts to the inverse fine unit class. -/
theorem perfectScalarCofiberBoundaryKOneClass_restrict :
    perfectOpenKRestrict j 1 (perfectScalarCofiberBoundaryKOneClass j K r q hq) =
      (perfectGlobalUnitKOneClass U q ((perfectComplexesRestrictOpenImmersion j).obj K))⁻¹ := by
  rw [perfectScalarCofiberBoundaryKOneClass_eq_inv, map_inv,
    perfectScalarForwardKOneClass_restrict]

/-- Rank one uses the actual structure sheaf and its native restriction isomorphism. -/
theorem perfectScalarForwardKOneClass_restrict_rankOne :
    perfectOpenKRestrict j 1
        (perfectScalarForwardKOneClass j (rankOnePerfectComplex X) r q hq) =
      perfectGlobalUnitKOneClass U q (rankOnePerfectComplex U) := by
  rw [perfectScalarForwardKOneClass_restrict]
  exact perfectGlobalUnitKOneClass_iso U q (rankOnePerfectComplexRestrictIso j)

/-- The structure-sheaf cofiber boundary is the inverse of the actual forward unit class. -/
theorem perfectScalarCofiberBoundaryKOneClass_restrict_rankOne :
    perfectOpenKRestrict j 1
        (perfectScalarCofiberBoundaryKOneClass j (rankOnePerfectComplex X) r q hq) =
      (perfectGlobalUnitKOneClass U q (rankOnePerfectComplex U))⁻¹ := by
  rw [perfectScalarCofiberBoundaryKOneClass_eq_inv, map_inv,
    perfectScalarForwardKOneClass_restrict_rankOne]

/-- A scalar restricting to the inverse unit gives the inverse of the original unit class. -/
theorem perfectScalarForwardKOneClass_restrict_inv (hq : j.appTop r = ↑(q⁻¹)) :
    perfectOpenKRestrict j 1 (perfectScalarForwardKOneClass j K r q⁻¹ hq) =
      (perfectGlobalUnitKOneClass U q ((perfectComplexesRestrictOpenImmersion j).obj K))⁻¹ := by
  rw [perfectScalarForwardKOneClass_restrict, perfectGlobalUnitKOneClass_inv]

attribute [colib_tag "COL-0305"] perfectScalarForwardKOneClass_restrict
  perfectScalarCofiberBoundaryKOneClass_restrict perfectScalarForwardKOneClass_restrict_rankOne

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarLaurentClassComparison.lean:49-83"
  "adaptation" "The original canonically rebased coarse restriction sends the actual forward
    scalar to the independent fine global-unit class; the cofiber orientation is inverse"]
  perfectScalarForwardKOneClass_restrict perfectScalarCofiberBoundaryKOneClass_restrict
  perfectScalarForwardKOneClass_restrict_rankOne
  perfectScalarCofiberBoundaryKOneClass_restrict_rankOne

end AlgebraicGeometry.Scheme.Modules
