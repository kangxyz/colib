/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.RelativeCurve.Pencils.AffineBaseNormalizedSections
open CategoryTheory AlgebraicGeometry Stacks.Ample
open AlgebraicGeometry.Scheme.RelativeCurvePencil
universe u
example {S Z : Scheme.{u}} (b : Z ⟶ S) [IsFinite b]
    (M : Z.Modules) [IsInvertibleModule Z M] (x : S) :
    ∃ U : S.affineOpens, x ∈ U.1 ∧
      Nonempty (M.restrict (b ⁻¹ᵁ U.1).ι ≅
        SheafOfModules.unit (b ⁻¹ᵁ U.1).toScheme.ringCatSheaf) :=
  exists_affine_wholeFiniteBoundary_frame b M x
#check baseRestrictedBoundaryFrame
#check exists_affineBase_normalized_sections
#check fieldMark_range_subset
#check wholeFiniteBoundary_fiber_retained
