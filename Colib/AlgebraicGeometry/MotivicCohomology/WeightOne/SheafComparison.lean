/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.OrdinaryShiftComparison
public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.QuasiIso
public import Colib.AlgebraicGeometry.Sites.Smooth.Units.UnitSheafification
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# The actual signed weight-one comparison on the whole smooth Nisnevich site

The map is the previously constructed geometric reduced norm, followed by the
proved contraction of actual global units. Native extension and signed shift
transport give the original ordinary comparison with Gm[0][-1]. There is no
assumed quasi-isomorphism and no replacement motivic complex.

Adapted from Motivic/Cohomology/WeightOne/SheafComparison.lean at revision
a6805c4a87cdfd7717dd7a94039246a167f15380, lines 28-59.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicSimplex

universe u

namespace AlgebraicGeometry.MotivicCohomology.WeightOne
open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The actual reduced norm followed by genuine units contraction. -/
def weightOneSheafChainComparison :
    (sheafifiedSingularChainsFunctor k (nisnevichTopology (Spec (.of k)))).obj
      (rawReducedTorus k) ⟶
        (ChainComplex.single₀ _).obj (largeUnitsSheaf (Spec (.of k))) :=
  reducedNormSheafMap k ≫ (unitSheafifiedSingularIso k).hom ≫
    (unitSingularSheafHomotopyEquiv k).hom

instance weightOneSheafChainComparison_quasiIso :
    QuasiIso (weightOneSheafChainComparison k) := by
  unfold weightOneSheafChainComparison
  infer_instance

/-- The map starts at the canonical complex and retains Mathlib's signed shift. -/
@[colib_tag "COL-0403"]
def weightOneSheafComparison :
    motivicSheafComplex k 1 ⟶
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (largeUnitsSheaf (Spec (.of k))))⟦(-1 : ℤ)⟧ :=
  (motivicSheafComplexOrdinaryShiftIso k 1).hom ≫
    (shiftFunctor _ (-1 : ℤ)).map
      (HomologicalComplex.extendMap (weightOneSheafChainComparison k)
        (ComplexShape.embeddingUpIntLE 0) ≫
      (HomologicalComplex.extendSingleIso (ComplexShape.embeddingUpIntLE 0)
        (largeUnitsSheaf (Spec (.of k))) 0 0 (by simp)).hom)

/-- The original full ordinary Nisnevich comparison is a quasi-isomorphism. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/WeightOne/SheafComparison.lean:28-59" "adaptation"
  "Actual geometric norm, units contraction, zero extension and canonical signed shift",
  colib_tag "COL-0403"]
instance weightOneSheafComparison_quasiIso : QuasiIso (weightOneSheafComparison k) := by
  unfold weightOneSheafComparison
  infer_instance

end AlgebraicGeometry.MotivicCohomology.WeightOne
