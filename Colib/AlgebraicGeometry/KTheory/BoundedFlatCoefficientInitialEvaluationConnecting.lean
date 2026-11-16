/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportConeStable
public import Colib.Topology.Prespectrum.FiberLiftConnecting
public import Colib.Topology.Prespectrum.ConeDescStableEquivalence

/-!
# The original initial coefficient boundary under geometric evaluation

The literal initial supported inclusion, coarse arrow and prescribed whole null
have a genuine stable fiber lift. Their intrinsic connecting map is natural for
the original evaluation square in every signed degree.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The original initial localization null gives a genuine stable fiber equivalence. -/
theorem boundedAboveFlatCoefficientInitialFiberLift_isStableEquivalence (a : Under R) :
    IsStableEquivalence (homotopyFiberLift
      ((boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
      ((boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f).app a)
      ((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy a)) :=
  homotopyFiberLift_isStableEquivalence_of_coneDesc _ _ _
    (prespectrum_mappingConeFiberComparison_isStableEquivalence
      ((boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f).app a))
    (boundedAboveFlatCoefficientSupportedOpenConeComparison_isStableEquivalence f a)

/-- The actual geometric acyclic lift is invertible in every degree at its literal endpoint. -/
theorem boundedAboveFlatCoefficientGeometricFiberLift_isStableEquivalence (a : Under R) :
    IsStableEquivalence (homotopyFiberLift
      (changeWeakPrespectrumMap (boundedAboveFlatPerfectOpenNested (schemeMap f a)))
      (acyclicInclusionPrespectrumMap (boundedAboveFlatPerfectOpenNested (schemeMap f a)))
      (acyclicPrespectrumNullhomotopy (boundedAboveFlatPerfectOpenNested (schemeMap f a)))) :=
  canonicalFiberPrespectrumMap_isStableEquivalence_of_weak _
    (boundedAboveFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence (schemeMap f a))

/-- The original evaluation square preserves the intrinsic initial signed boundary. -/
theorem boundedAboveFlatCoefficientInitialConnecting_evaluation (a : Under R) (d : ℤ) :
    let := boundedAboveFlatCoefficientInitialFiberLift_isStableEquivalence f a d
    let := boundedAboveFlatCoefficientGeometricFiberLift_isStableEquivalence f a d
    stableFiberLiftConnecting
        ((boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f).app a)
        ((boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
        ((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy a) d ≫
        (stableHomotopyFunctor d).map (prespectrumMap (supportAcyclicModelMap f a)) =
      (stableHomotopyFunctor (d + 1)).map (prespectrumMap (openEvaluationModelMap f a)) ≫
        stableFiberLiftConnecting
          (acyclicInclusionPrespectrumMap (boundedAboveFlatPerfectOpenNested (schemeMap f a)))
          (changeWeakPrespectrumMap (boundedAboveFlatPerfectOpenNested (schemeMap f a)))
          (acyclicPrespectrumNullhomotopy
            (boundedAboveFlatPerfectOpenNested (schemeMap f a))) d := by
  let := boundedAboveFlatCoefficientInitialFiberLift_isStableEquivalence f a d
  let := boundedAboveFlatCoefficientGeometricFiberLift_isStableEquivalence f a d
  apply stableFiberLiftConnecting_naturality
    ((boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f).app a)
    ((boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
    (acyclicInclusionPrespectrumMap (boundedAboveFlatPerfectOpenNested (schemeMap f a)))
    (changeWeakPrespectrumMap (boundedAboveFlatPerfectOpenNested (schemeMap f a)))
    ((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy a)
    (acyclicPrespectrumNullhomotopy (boundedAboveFlatPerfectOpenNested (schemeMap f a)))
    (prespectrumMap (supportAcyclicModelMap f a))
    (prespectrumMap (ambientEvaluationModelMap a))
    (prespectrumMap (openEvaluationModelMap f a))
  · exact (Arrow.w (supportEvaluationSquare f a)).symm
  · exact ((prespectrumFunctor.map_comp _ _).symm.trans
      ((congrArg prespectrumFunctor.map (evaluation_changeWeak f a)).trans
        (prespectrumFunctor.map_comp _ _))).symm
  · exact null_evaluation f a

end AlgebraicGeometry.Scheme.Modules
