/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFiberLocalizationModels
public import Colib.Topology.Prespectrum.FiberLiftConnecting
public import Colib.Topology.Prespectrum.ConeDescStableEquivalence

/-!
# The original initial auxiliary boundary under native acyclic conversion

The literal initial intersection-support inclusion, coarse arrow and prescribed whole null
have a genuine stable fiber lift. Their intrinsic connecting map is natural for
the original native conversion square in every signed degree.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS
open Topology Topology.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The original initial localization null gives a genuine stable fiber equivalence. -/
theorem boundedAboveFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence (a : Under R) :
    IsStableEquivalence (homotopyFiberLift
      ((boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a)
      ((boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a)
      ((boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a)) :=
  homotopyFiberLift_isStableEquivalence_of_coneDesc _ _ _
    (prespectrum_mappingConeFiberComparison_isStableEquivalence
      ((boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a))
    (boundedAboveFlatCoefficientSupportedFiberOpenConeComparison_isStableEquivalence f T a)

/-- The actual native acyclic lift is invertible in every degree at its literal endpoint. -/
theorem boundedAboveFlatCoefficientAuxiliaryNativeFiberLift_isStableEquivalence (a : Under R) :
    IsStableEquivalence (homotopyFiberLift
      (changeWeakPrespectrumMap (boundedAboveFlatCoefficientSupportedOpenNested f T a))
      (acyclicInclusionPrespectrumMap (boundedAboveFlatCoefficientSupportedOpenNested f T a))
      (acyclicPrespectrumNullhomotopy
            (boundedAboveFlatCoefficientSupportedOpenNested f T a))) :=
  canonicalFiberPrespectrumMap_isStableEquivalence_of_weak _
    (boundedAboveFlatCoefficientSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence
            f T a)

/-- The original native conversion square preserves the intrinsic initial signed boundary. -/
theorem boundedAboveFlatCoefficientAuxiliaryInitialConnecting_native (a : Under R) (d : ℤ) :
    let := boundedAboveFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a d
    let := boundedAboveFlatCoefficientAuxiliaryNativeFiberLift_isStableEquivalence f T a d
    stableFiberLiftConnecting
        ((boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a)
        ((boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a)
        ((boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a) d ≫
        (stableHomotopyFunctor d).map
      (prespectrumMap (supportedNativeFiberAcyclicModelMap f T a)) =
      (stableHomotopyFunctor (d + 1)).map (prespectrumMap (supportedNativeCoarseModelMap f T a)) ≫
        stableFiberLiftConnecting
          (acyclicInclusionPrespectrumMap (boundedAboveFlatCoefficientSupportedOpenNested f T a))
          (changeWeakPrespectrumMap (boundedAboveFlatCoefficientSupportedOpenNested f T a))
          (acyclicPrespectrumNullhomotopy
            (boundedAboveFlatCoefficientSupportedOpenNested f T a)) d := by
  let := boundedAboveFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a d
  let := boundedAboveFlatCoefficientAuxiliaryNativeFiberLift_isStableEquivalence f T a d
  apply stableFiberLiftConnecting_naturality
    ((boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a)
    ((boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a)
    (acyclicInclusionPrespectrumMap (boundedAboveFlatCoefficientSupportedOpenNested f T a))
    (changeWeakPrespectrumMap (boundedAboveFlatCoefficientSupportedOpenNested f T a))
    ((boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a)
    (acyclicPrespectrumNullhomotopy
            (boundedAboveFlatCoefficientSupportedOpenNested f T a))
    (prespectrumMap (supportedNativeFiberAcyclicModelMap f T a))
    (prespectrumMap (supportedNativeAmbientModelMap T a))
    (prespectrumMap (supportedNativeCoarseModelMap f T a))
  · exact (Arrow.w (supportedNativeFiberEvaluationSquare f T a)).symm
  · exact ((prespectrumFunctor.map_comp _ _).symm.trans
      ((congrArg prespectrumFunctor.map (supportedNativeEvaluation_changeWeak f T a)).trans
        (prespectrumFunctor.map_comp _ _))).symm
  · exact supportedNativeFiberNull_evaluation f T a

end AlgebraicGeometry.Scheme.Modules
