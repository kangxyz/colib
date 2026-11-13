/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.EtaleCounitAlgebraicallyClosedReduction
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.EtaleTorsionContract
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.EtaleCounitPolynomialCondition
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.PolynomialTailSimultaneousInduction
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.PolynomialTailToAffineStructural

/-! # The actual étale rigidity counit

UNVERIFIED final integration candidate. Its positive-dimensional production
chain and this file require CI validation. The exact reduction and source
conditions are retained; no completed public endpoint is asserted yet.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open QuadraticIncidence.InfinityChart
universe u
namespace AlgebraicGeometry.PresheafWithTransfers

local instance {K : Type u} [Field K] :
    IsAffine (AlgebraicGeometry.Scheme.SmoothSite.base (Spec (.of K))).left :=
  inferInstanceAs (IsAffine (Spec (.of K)))

/-- Coefficient homotopy invariance and prime-to-characteristic torsion make the
actual full-small-étale extension counit invertible on the actual sheafification. -/
theorem isIso_fullSmallEtale_sheafification_counit_of_A1Invariant
    (K : Type u) [Field K] (P : PresheafWithTransfers.{u + 1} K)
    (hP : IsA1Invariant P) (n : ℕ)
    (hn : ∀ (V : SmoothSite (Spec (.of K)))
      (z : sections P ((Cor.graphFunctor K).obj V)), (n + 1) • z = 0)
    (hnK : IsUnit ((n + 1 : ℕ) : K)) :
    let F := (presheafToSheaf (SmoothSite.etaleTopology (Spec (.of K)))
      AddCommGrpCat.{u + 1}).obj ((toPresheaf K).obj P)
    IsIso ((fullSmallEtaleAdjunction
      (AlgebraicGeometry.Scheme.SmoothSite.base (Spec (.of K)))).counit.app F) := by
  apply (isIso_fullSmallEtale_sheafification_counit_iff_algebraicallyClosedSeparableNeighborhood
    P (n + 1) hnK (torsionBy_of_succ_nsmul P n hn)).mpr
  exact counit_separable_condition_of_polynomial_tails K P
    (fun Ω _ _ d => polynomialTailIsomorphisms_all_dimensions K Ω P hP n hn hnK d)

end AlgebraicGeometry.PresheafWithTransfers
