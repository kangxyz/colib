/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.SheafComparison

open CategoryTheory AlgebraicGeometry AlgebraicSimplex
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.PresheafWithTransfers AlgebraicGeometry.MotivicCohomology.WeightOne

universe u

noncomputable section

variable (k : Type u) [Field k]

example : weightOneSheafChainComparison k = reducedNormSheafMap k ≫
    (unitSheafifiedSingularIso k).hom ≫ (unitSingularSheafHomotopyEquiv k).hom := rfl

example : QuasiIso (weightOneSheafChainComparison k) := inferInstance

example : motivicSheafComplex k 1 ≅
    (((sheafifiedSingularChainsFunctor k (nisnevichTopology (Spec (.of k)))).obj
      (rawReducedTorus k)).extend (ComplexShape.embeddingUpIntLE 0))⟦(-1 : ℤ)⟧ :=
  motivicSheafComplexOrdinaryShiftIso k 1

example : motivicSheafComplex k 1 ⟶
    ((CochainComplex.singleFunctor _ 0).obj
      (largeUnitsSheaf (Spec (.of k))))⟦(-1 : ℤ)⟧ := weightOneSheafComparison k

example : QuasiIso (weightOneSheafComparison k) := inferInstance

example (r : ℕ) :
    (motivicComplexPlacementIso k 1).hom.f ((1 : ℤ) - r) =
      (-1 : ℤ) ^ r •
        ((singularSheafCochainXIso k (reducedTorus k 1) 1 r).hom ≫
          (motivicComplexXIso k 1 r).inv) := motivicComplexPlacementIso_one_hom_f k r
