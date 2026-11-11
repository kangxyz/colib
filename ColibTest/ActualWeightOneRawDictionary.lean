/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.RawClasses
import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.FieldComparisonMap

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.PresheafWithTransfers AlgebraicGeometry.MotivicCohomology.WeightOne

universe w u
noncomputable section
variable (k : Type u) [Field k]

example (q : ℕ) : motivicRawBaseComplex k q ≅ motivicBaseComplex k q :=
  motivicRawBaseComplexIso k q

example : Function.Surjective (rawClass k) := rawClass_surjective k

example (x : (motivicRawBaseComplex k 1).X 0) :
    rawClass k ((motivicRawBaseComplex k 1).d 0 1 x) = 0 := rawClass_boundary k x

example : (motivicRawBaseComplex k 1).d 0 1 =
    -((motivicRawBaseComplexXIso k 1 1).hom ≫
      (singularObj (reducedTorus k 1) (point k)).d 1 0 ≫
        (motivicRawBaseComplexXIso k 1 0).inv) := raw_d_zero_one k

example (a : kˣ) : cycleClass k ((Cor.graphFunctor k).map (rationalPoint k a)) =
    graphUnitClass k a := cycleClass_graph k a

example (p : ℤ) : (motivicRawBaseComplex k 1).homology p ≅
    (shiftedUnitsBaseComplex k).homology p := rawWeightOneHomologyIso k p

example (i : ℤ) : (rawWeightOneComparison k).f i =
    (motivicRawBaseComplexIso k 1).hom.f i ≫
      ((weightOneSheafComparison k).f i).hom.app (op (base (Spec (.of k)))) :=
  rawWeightOneComparison_f k i

example : Function.Bijective (rawComparisonNorm k) := rawComparisonNorm_bijective k

example (x : (motivicRawBaseComplex k 1).cycles 1) :
    rawComparisonNorm k ((motivicRawBaseComplex k 1).homologyπ 1 x) =
      shiftedUnitsBaseHomologyEquiv k ((shiftedUnitsBaseComplex k).homologyπ 1
        (HomologicalComplex.cyclesMap (rawWeightOneComparison k) 1 x)) :=
  rawComparisonNorm_class k x

variable [HasDerivedCategory.{w}
  (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

example (p : ℤ) (q : ℕ) : motivicCohomology k p q (base (Spec (.of k))) ≃+
    (motivicRawBaseComplex k q).homology p := motivicRawBaseEvaluationComparison k p q

example (a : kˣ) : motivicRawBaseEvaluationComparison k 1 1 (integralGraphUnitClass k a) =
    graphUnitClass k a := integralGraphUnitClass_comparison k a

example (p : ℤ) (x : motivicCohomology k p 1 (base (Spec (.of k)))) :
    hypercohomologyBaseFieldAddEquiv k (shiftedUnitsSheafComplex k) p
      (derivedWeightOneComparison k p x) =
      (rawWeightOneHomologyIso k p).hom (motivicRawBaseEvaluationComparison k p 1 x) :=
  rawWeightOneComparison_derived k p x
