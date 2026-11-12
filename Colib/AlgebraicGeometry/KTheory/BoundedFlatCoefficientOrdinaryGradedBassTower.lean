/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenBassStages
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenRestrictionStages
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryGradedSeedCompatibility
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryGradedBassVanishing
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenConeStable
public import Colib.KTheory.Bass.ModelDiagramIterateCofiberPreservation
public import Colib.KTheory.Bass.StrictDiagramIterateNullTimeSlice
public import Colib.Topology.Prespectrum.ConeDiagramDescent

/-! # Actual original ordinary graded Bass stabilization

The ordinary coefficient models and original seeds are unchanged. This slice owns the
actual graded stages, full nulls, all-signed vanishing and cone comparison. The ordinary
restriction maps, their cone-fiber comparison and final restriction stability belong to
separate owners. No auxiliary support parameter is introduced.
-/
@[expose] public section
noncomputable section
open CommRingCat.PolynomialLaurent
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]

/-- The same original q transformation at every finite stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTower.lean:100"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
def boundedAboveFlatCoefficientOpenBassGrading (i : ℕ) :
    boundedAboveFlatCoefficientFullOpenBassDiagram f i ⟶
      boundedAboveFlatCoefficientGradedOpenBassDiagram f i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f)

/-- The actual q seed square supplies every unchanged finite transition equation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTower.lean:107"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
theorem boundedAboveFlatCoefficientOpenBassGrading_transition (i : ℕ) :
    boundedAboveFlatCoefficientOpenBassGrading f i ≫
      boundedAboveFlatCoefficientGradedOpenBassTransition f i =
      boundedAboveFlatCoefficientFullOpenBassTransition f i ≫
        boundedAboveFlatCoefficientOpenBassGrading f (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientFullOpenBassSeed f) (boundedAboveFlatCoefficientGradedOpenBassSeed
      f)
    (boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f)
    (boundedAboveFlatCoefficientFullOpenBassSeed_grading f) i).symm

/-- Iterate precisely the original canonical whole coefficient-natural localization null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTower.lean:117"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
def boundedAboveFlatCoefficientOpenBassGradingNull (i : ℕ) :
    DiagramNullHomotopy (boundedAboveFlatCoefficientOpenBassRestriction f i)
      (boundedAboveFlatCoefficientOpenBassGrading f i) :=
  strictDiagramIterateNull (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientOpenGradingDiagramNull f) i

/-- The whole finite localization null preserves original seed transitions at every time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTower.lean:124"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
theorem boundedAboveFlatCoefficientOpenBassGradingNull_transition
    (i : ℕ) (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientOpenBassDiagram f i).obj a).space m) :
    ((boundedAboveFlatCoefficientGradedOpenBassTransition f i).app a).map m
      (((boundedAboveFlatCoefficientOpenBassGradingNull f i).homotopy a).level m (s, x)) =
    ((boundedAboveFlatCoefficientOpenBassGradingNull f (i + 1)).homotopy a).level m
      (s, ((boundedAboveFlatCoefficientOpenBassTransition f i).app a).map m x) :=
  (strictDiagramIterateNull_transition (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientOpenGradingDiagramNull f)
    (boundedAboveFlatCoefficientOpenBassSeed f) (boundedAboveFlatCoefficientGradedOpenBassSeed f)
    (fun s ↦ boundedAboveFlatCoefficientOpenGradingNullTimeSlice_seed f s) i a m s x).symm

/-- The actual finite original cone descends along the same complete iterated localization null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTower.lean:137"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
def boundedAboveFlatCoefficientOpenBassConeComparison (i : ℕ) :
    mappingConeDiagram (boundedAboveFlatCoefficientOpenBassRestriction f i) ⟶
      boundedAboveFlatCoefficientGradedOpenBassDiagram f i :=
  mappingConeDescTransformation (boundedAboveFlatCoefficientOpenBassRestriction f i)
    (boundedAboveFlatCoefficientOpenBassGrading f i)
    (boundedAboveFlatCoefficientOpenBassGradingNull f i).homotopy
    (boundedAboveFlatCoefficientOpenBassGradingNull f i).naturality

/-- The original finite cone inclusion has precisely the actual q_i face. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTower.lean:146"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
theorem boundedAboveFlatCoefficientOpenBassConeComparison_inclusion (i : ℕ) (a : Under R) :
    mappingConeInclusion ((boundedAboveFlatCoefficientOpenBassRestriction f i).app a) ≫
        (boundedAboveFlatCoefficientOpenBassConeComparison f i).app a =
      (boundedAboveFlatCoefficientOpenBassGrading f i).app a := mappingConeInclusion_desc _ _ _

variable [QuasiSeparatedSpace Q.left]

/-- Actual finite Model excision propagates the original initial stable cone descent. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTower.lean:178"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
theorem boundedAboveFlatCoefficientOpenBassConeComparison_isStableEquivalence
    (i : ℕ) (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientOpenBassConeComparison f i).app a) :=
  modelDiagramIterateCofiberDesc_isStableEquivalence (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientOpenModelFunctor f)
      (boundedAboveFlatCoefficientFullOpenModelFunctor f)
    (boundedAboveFlatCoefficientGradedOpenModelFunctor f)
    (boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f)
    (boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f)
    (boundedAboveFlatCoefficientOpenGradingDiagramNull f)
    (fun a ↦ boundedAboveFlatCoefficientOpenConeComparison_isStableEquivalence f a) i a

end AlgebraicGeometry.Scheme.Modules
