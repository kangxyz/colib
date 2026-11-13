/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.SheafComparison
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.CoefficientQuotientQuasiIso
public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.QuasiIso

/-!
# The original finite weight-one complex and the actual units cone

This consumes the completed geometric weight-one comparison. Both arrows of
the resulting coefficient-model zigzag are actual quasi-isomorphisms. The
units cone still needs the correctly sited Kummer comparison before it can be
identified with roots of unity; that identification is not assumed here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.MotivicCohomology.WeightOne
open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The existing weight-one target with its genuine signed shift. -/
def weightOneUnitsComplex :=
  ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    (largeUnitsSheaf (Spec (.of k))))⟦(-1 : ℤ)⟧

/-- The actual multiplication cone of the shifted units complex. -/
def weightOneFiniteUnitsComplex (n : ℕ) :=
  CochainComplex.finiteCoefficients (weightOneUnitsComplex k) n

/-- The completed geometric norm induces the original finite-coefficient comparison. -/
def weightOneFiniteSheafComparison (n : ℕ) :
    motivicFiniteSheafComplex k 1 n ⟶ weightOneFiniteUnitsComplex k n :=
  CochainComplex.finiteCoefficients.map n (weightOneSheafComparison k)

/-- The finite weight-one map is a genuine quasi-isomorphism, with no Kummer assumption. -/
theorem weightOneFiniteSheafComparison_quasiIso (n : ℕ) :
    QuasiIso (weightOneFiniteSheafComparison k n) :=
  CochainComplex.finiteCoefficients.quasiIso_map n (weightOneSheafComparison k)

/-- The finite weight-one comparison retains the original integral reduction. -/
@[reassoc]
theorem weightOneFiniteSheafComparison_integral (n : ℕ) :
    CochainComplex.finiteCoefficients.integral (motivicSheafComplex k 1) n ≫
        weightOneFiniteSheafComparison k n =
      weightOneSheafComparison k ≫
        CochainComplex.finiteCoefficients.integral (weightOneUnitsComplex k) n :=
  CochainComplex.finiteCoefficients.integral_naturality n (weightOneSheafComparison k)

/-- The original positive Bockstein and the signed shift are unchanged. -/
@[reassoc]
theorem weightOneFiniteSheafComparison_bockstein (n : ℕ) :
    weightOneFiniteSheafComparison k n ≫
        CochainComplex.finiteCoefficients.bockstein (weightOneUnitsComplex k) n =
      CochainComplex.finiteCoefficients.bockstein (motivicSheafComplex k 1) n ≫
        (weightOneSheafComparison k)⟦(1 : ℤ)⟧' :=
  CochainComplex.finiteCoefficients.bockstein_naturality n (weightOneSheafComparison k)

variable [HasDerivedCategory
  (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The actual strict coefficient quotient and the units cone are derived-isomorphic. -/
@[colib_tag "COL-1231",
  colib_ref "mathlib_stable_localization_pin"
    "Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean:514-517" "specialization"
    "Apply native two-out-of-three to the completed weight-one map of multiplication cones"]
def weightOneCoefficientQuotientUnitsIso (n : ℕ) (hn : n ≠ 0) :
    DerivedCategory.Q.obj (motivicCoefficientQuotient k 1 n) ≅
      DerivedCategory.Q.obj (weightOneFiniteUnitsComplex k n) := by
  have := motivicFiniteToCoefficientQuotient_quasiIso k 1 n hn
  have := weightOneFiniteSheafComparison_quasiIso k n
  exact (asIso (DerivedCategory.Q.map (motivicFiniteToCoefficientQuotient k 1 n))).symm ≪≫
    asIso (DerivedCategory.Q.map (weightOneFiniteSheafComparison k n))

end AlgebraicGeometry.MotivicCohomology.WeightOne
