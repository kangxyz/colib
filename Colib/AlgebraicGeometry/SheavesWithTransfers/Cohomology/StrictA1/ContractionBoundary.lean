/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ContractionInvariance
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.ContractionGenericZero
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.Inputs
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.GenericOpenVanishing

/-!
# Vanishing of the original cohomology boundary

The positive contraction has genuine generic open zeros. Integral-affine
local vanishing kills its ordinary small-site sheafification. The canonical
epimorphism then kills the actual cohomological zero-section boundary.

Adapted from `Motivic/Cohomology/A1/Contraction/CohomologyInputs.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SheafCohomology

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary

variable {k : Type u} [Field k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The actual small-site source of the canonical boundary vanishes. -/
theorem isZero_smallSheafify_contraction_succ_of_integralAffineLocalZero
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) :
    IsZero ((presheafToSheaf (EtaleSeparatedFiniteType.nisnevichTopology X.left)
      AddCommGrpCat.{u + 1}).obj
      ((EtaleSeparatedFiniteType.toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj
        (PresheafWithTransfers.contraction (withTransfers k F (n + 1))))) :=
  EtaleSeparatedFiniteType.isZero_sheafify_of_generic_open_zeros hD _
    (PresheafWithTransfers.contraction_isA1Invariant _ hP)
    (contraction_hasGenericOpenZeros_succ F n hP) X

/-- Local vanishing and the canonical coefficient epimorphism give zero
boundary in the positive degree in which the coefficient is invariant. -/
theorem isZero_zeroSectionBoundary_succ_of_coefficient_inputs
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
    (hE : OriginalPresheaf.CanonicalBoundaryEpi k)
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) :
    IsZero (OriginalPresheaf.zeroSectionBoundary X (withTransfers k F (n + 1))) := by
  let := hE X (withTransfers k F (n + 1)) hP
  exact IsZero.of_epi (OriginalPresheaf.contractionToBoundary X (withTransfers k F (n + 1)))
    (isZero_smallSheafify_contraction_succ_of_integralAffineLocalZero hD F n hP X)

end AlgebraicGeometry.SheafCohomology
