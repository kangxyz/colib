/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassEvaluation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineBassStep
public import Colib.Topology.Prespectrum.StrictSquarePointHEP
public import Colib.KTheory.Waldhausen.Iterated.PointHEP


/-!
# Literal point topology for the original one-step Bass evaluation comparison

The strict section span and the original raw geometric span have genuine point HEP at every
level, including zero. The actual two cones and raw parameter-looped step inherit it. These
are the exact objects of original evaluation; no strict geometric coefficient diagram or
replacement span is used, and T1 is used only where actual loop-point closure requires it.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.RingedSpace Topology
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual strict section span has HEP at every original chosen point. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluationTopology.lean:29-38"
  "adaptation" "Original actual-map comparison with the native whole objects retained"]
theorem boundedAboveFlatAffineSectionBassSpan_point_homotopyExtensionProperty
    (R : CommRingCat.{u}) (n : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((StrictSquare.span (boundedAboveFlatAffineSectionBassSquare R)).point n))) :=
  StrictSquare.span_point_homotopyExtensionProperty _ n
    (prespectrum_point_homotopyExtensionProperty (boundedAboveFlatAffineSectionModel R) n)
    (prespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatAffineSectionModel (.of (Polynomial R))) n)
    (prespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatAffineSectionModel (.of (Polynomial R))) n)

/-- The unchanged raw bounded-flat geometric span has genuine HEP, also at level zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluationTopology.lean:41-52"
  "adaptation" "Original actual-map comparison with the native whole objects retained"]
theorem boundedAboveFlatBassSpan_point_homotopyExtensionProperty (R : CommRingCat.{u}) (n : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((HomotopyPushout.prespectrum
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R))).point n))) :=
  HomotopyPushout.point_homotopyExtensionProperty _ _ n
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatPerfectWaldhausen (Spec (.of (Polynomial R))).toRingedSpace) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatPerfectWaldhausen (Spec (.of (Polynomial R))).toRingedSpace) n)

/-- The actual strict section cone retains its literal well-based point in every degree. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluationTopology.lean:55-63"
  "adaptation" "Original actual-map comparison with the native whole objects retained"]
theorem boundedAboveFlatAffineSectionBassCone_point_homotopyExtensionProperty
    (R : CommRingCat.{u}) (n : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((boundedAboveFlatAffineSectionBassCone R).point n))) :=
  ReducedMappingCone.point_homotopyExtensionProperty _ _ _
    ((StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare R)).map_point n)
    (boundedAboveFlatAffineSectionBassSpan_point_homotopyExtensionProperty R n)
    (prespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatAffineSectionModel (.of (LaurentPolynomial R))) n)

/-- The original raw geometric Bass cone retains HEP at every actual chosen point. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluationTopology.lean:66-73"
  "adaptation" "Original actual-map comparison with the native whole objects retained"]
theorem boundedAboveFlatBassCone_point_homotopyExtensionProperty (R : CommRingCat.{u}) (n : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((mappingCone (boundedAboveFlatBassSquareComparison R)).point n))) :=
  ReducedMappingCone.point_homotopyExtensionProperty _ _ _
    ((boundedAboveFlatBassSquareComparison R).map_point n)
    (boundedAboveFlatBassSpan_point_homotopyExtensionProperty R n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))).toRingedSpace) n)

/-- The unchanged raw geometric one-step parameter loop is well-based at every level. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluationTopology.lean:76-81"
  "adaptation" "Original actual-map comparison with the native whole objects retained"]
theorem boundedAboveFlatAffineBassStep_point_homotopyExtensionProperty
    (R : CommRingCat.{u}) (n : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((boundedAboveFlatAffineBassStep R).point n))) :=
  parameterLooping_point_homotopyExtensionProperty
    (mappingCone (boundedAboveFlatBassSquareComparison R))
    n isClosed_singleton (boundedAboveFlatBassCone_point_homotopyExtensionProperty R n)

end AlgebraicGeometry.Scheme.Modules
