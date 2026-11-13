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

For an A¹-invariant presheaf with transfers annihilated by a fixed positive
integer invertible in the ground field, the canonical full-small/smooth étale
adjunction counit is an isomorphism on its actual étale sheafification.
Polynomial-tail induction supplies the exact original-neighborhood condition;
no perfection assumption or replacement presheaf over extension fields is used.
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
@[colib_tag "COL-1222", colib_ref "MVW2006" "Lecture 7, Theorem 7.20, p. 51" "adaptation"
  "Fixed invertible positive exponent; canonical full-small/smooth etale counit"]
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
