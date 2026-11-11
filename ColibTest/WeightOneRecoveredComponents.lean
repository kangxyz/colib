/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.FieldComponent
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite AlgebraicSimplex
open AlgebraicGeometry.MotivicCohomology.WeightOne
open AlgebraicGeometry.PresheafWithTransfers
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
universe u
variable (k : Type u) [Field k]
example :
    (shiftedUnitsBaseComplex k).homologyπ 1 ≫ (shiftedUnitsBaseHomologyIso k).hom =
      (shiftedUnitsBaseComplex k).iCycles 1 ≫ (shiftedUnitsBaseXIso k).hom :=
  homologyπ_shiftedUnitsBaseHomologyIso k
example :
    rawClass k ≫ (rawWeightOneHomologyIso k 1).hom ≫
      (shiftedUnitsBaseHomologyIso k).hom =
        (rawWeightOneComparison k).f 1 ≫ (shiftedUnitsBaseXIso k).hom :=
  rawClass_rawWeightOneComparison k
example (s : (rawReducedTorus k).obj (op (base (Spec (.of k))))) :
    (shiftedUnitsBaseXIso k).hom
      ((rawWeightOneComparison k).f 1
        ((motivicRawBaseComplexXIso k 1 0).inv
          ((rawReducedTorus k).map
            (productFst (base (Spec (.of k))) (smoothSiteObj k 0)).op s))) =
      (reducedNorm k).app (op (base (Spec (.of k)))) s :=
  rawWeightOneComparison_zero_pullback k s
