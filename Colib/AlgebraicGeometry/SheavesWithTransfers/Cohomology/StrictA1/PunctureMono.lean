/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.Field
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.H1ChartRestriction
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.PositiveRestriction
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Puncture.CartierTransport

/-! # Cartier puncture monicity from strictly lower degrees

The original coefficient local-zero theorem and the canonical boundary
epimorphism give monicity in degree one. In higher degrees the lower-degree
hypothesis also applies to the actual contraction.

Adapted from the degree-one and higher-degree branches of
`Motivic/Cohomology/A1/StrictInvariance` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- For every HI coefficient the actual marked Cartier puncture restriction is
monic once the strictly lower degrees are HI for all such coefficients. -/
theorem smoothCartierPunctureRestrictionMono_of_boundary_epi
    (hEpi : Boundary.OriginalPresheaf.CanonicalBoundaryEpi k) (n : ℕ)
    (hLow : ∀ (G : SheafWithTransfers.{u + 1} k), G.obj.IsA1Invariant →
      ∀ q : ℕ, 0 < q → q < n + 1 → (SheafCohomology.withTransfers k G q).IsA1Invariant)
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) :
    SmoothCartierPunctureRestrictionMono F (n + 1) := by
  have hD : PresheafWithTransfers.IntegralAffineLocalZero k :=
    PresheafWithTransfers.integralAffineLocalZero_of_field k
  refine smoothCartierPunctureRestrictionMono_of_cylinder_charts F (n + 1) ?_
  dsimp only
  intro D E W b _ d j _ q hd hj K _ c
  cases n with
  | zero =>
    exact Boundary.pointedCylinderRestriction_H1_colimit_mono_of_chart
      hD hEpi D b F j q hj hF (relativeFieldPoint (c ≫ d.left) K (𝟙 _))
  | succ n =>
    have hContract := hLow (SheafWithTransfers.contraction F hF)
      (SheafWithTransfers.contraction_isA1Invariant F hF) (n + 1) (Nat.succ_pos n) (by omega)
    exact Boundary.pointedCylinderRestriction_positive_colimit_mono_of_chart
      hD hEpi D b F j q hj d hd hF K c n hContract (hLow F hF)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
