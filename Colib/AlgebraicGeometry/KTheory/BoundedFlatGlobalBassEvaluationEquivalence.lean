/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluation
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationEquivalence
public import Colib.Topology.Prespectrum.StrictSquarePointHEP
public import Colib.KTheory.Waldhausen.Iterated.PointHEP
public import Colib.Topology.Prespectrum.PushoutHomotopySquareEquivalence
public import Colib.Topology.Prespectrum.ConeSquareLevelWeakEquivalence
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.WeakEquivalence
public import Colib.Util.References

/-!
# Weak and stable equivalence of the actual one-step global Bass evaluation

Original normalized evaluation is a complete weak equivalence at every level. The genuine
point HEP of the original spectra and spans makes the actual overlap-descended span, cone
and parameter-loop maps complete weak equivalences. No geometric excision premise is added.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation
open GlobalSectionChangeIndex

/-- The original global normalized evaluation is completely weak at every spectrum level. -/
theorem evaluation_level_isWeakHomotopyEquivalence (X : Scheme.{u}) (n : ℕ) :
    IsWeakHomotopyEquivalence ((evaluation X).map n) :=
  evaluationModel_level_isWeakHomotopyEquivalence (op X) n

/-- The actual strict section span retains its original well-based point. -/
theorem sectionSpan_point_homotopyExtensionProperty (X : Scheme.{u}) (n : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u+2}
      ((StrictSquare.span (sectionSquare X)).point n))) :=
  StrictSquare.span_point_homotopyExtensionProperty _ n
    (prespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatGlobalSectionModelFunctor.obj (op X)) n)
    (prespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatGlobalSectionModelFunctor.obj (op (polynomial.obj X))) n)
    (prespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatGlobalSectionModelFunctor.obj (op (polynomial.obj X))) n)

/-- The actual raw polynomial span has genuine point HEP at every level, including zero. -/
theorem rawSpan_point_homotopyExtensionProperty (X : Scheme.{u}) (n : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u+2}
      ((GlobalRawBass.span X).point n))) :=
  HomotopyPushout.point_homotopyExtensionProperty _ _ n
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatPerfectWaldhausen (polynomial.obj X).toRingedSpace) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatPerfectWaldhausen (polynomial.obj X).toRingedSpace) n)

/-- The unchanged whole-track polynomial-span evaluation is completely weak at every level. -/
theorem spanEvaluation_level_isWeakHomotopyEquivalence (X : Scheme.{u}) (n : ℕ) :
    IsWeakHomotopyEquivalence ((spanEvaluation X).map n) :=
  HomotopyPushout.mapOfHomotopies_level_isWeakHomotopyEquivalence
    (sectionMap (projection.app X)) (sectionMap (projection.app X))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
    (evaluation X) (evaluation (polynomial.obj X)) (evaluation (polynomial.obj X))
    (evaluationComparison (projection.app X)) (evaluationComparison (projection.app X)) n
    (prespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatGlobalSectionModelFunctor.obj (op X)) n)
    (prespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatGlobalSectionModelFunctor.obj (op (polynomial.obj X))) n)
    (prespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatGlobalSectionModelFunctor.obj (op (polynomial.obj X))) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatPerfectWaldhausen (polynomial.obj X).toRingedSpace) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatPerfectWaldhausen (polynomial.obj X).toRingedSpace) n)
    (evaluation_level_isWeakHomotopyEquivalence X n)
    (evaluation_level_isWeakHomotopyEquivalence (polynomial.obj X) n)
    (evaluation_level_isWeakHomotopyEquivalence (polynomial.obj X) n)

/-- The literal cone evaluation with the proved original overlap is completely weak. -/
theorem coneEvaluation_level_isWeakHomotopyEquivalence (X : Scheme.{u}) (n : ℕ) :
    IsWeakHomotopyEquivalence ((coneEvaluation X).map n) :=
  mappingConeSquareMap_level_isWeakHomotopyEquivalence
    (StrictSquare.comparison (sectionSquare X)) (GlobalRawBass.comparison X)
    (spanEvaluation X) (evaluation (laurent.obj X)) (comparisonHomotopy X) n
    (sectionSpan_point_homotopyExtensionProperty X n)
    (prespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatGlobalSectionModelFunctor.obj (op (laurent.obj X))) n)
    (rawSpan_point_homotopyExtensionProperty X n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedAboveFlatPerfectWaldhausen (laurent.obj X).toRingedSpace) n)
    (spanEvaluation_level_isWeakHomotopyEquivalence X n)
    (evaluation_level_isWeakHomotopyEquivalence (laurent.obj X) n)

/-- Parameter looping preserves every component of the actual cone evaluation, also at zero. -/
theorem stepEvaluation_level_isWeakHomotopyEquivalence (X : Scheme.{u}) (n : ℕ) :
    IsWeakHomotopyEquivalence ((stepEvaluation X).map n) :=
  basedLoopMap_isWeakHomotopyEquivalence ((coneEvaluation X).map n)
    ((coneEvaluation X).map_point n) (coneEvaluation_level_isWeakHomotopyEquivalence X n)

/-- The actual strict-section to raw Bass step evaluation is stable in every signed degree. -/
@[colib_tag "COL-1342",
  colib_ref "ThomasonTrobaugh1990" "Sections 6.3–6.4" "background"
    "The Bass construction; the evaluation comparison concerns these formal models."]
theorem stepEvaluation_isStableEquivalence (X : Scheme.{u}) :
    IsStableEquivalence (stepEvaluation X) :=
  isStableEquivalence_of_levelwise _ (stepEvaluation_level_isWeakHomotopyEquivalence X)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation
