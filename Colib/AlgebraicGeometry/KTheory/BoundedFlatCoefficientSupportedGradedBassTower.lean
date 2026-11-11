/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenBassStages
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenSeedCompatibility
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenConeStable
public import Colib.KTheory.Bass.ModelDiagramIterateCofiberPreservation
public import Colib.KTheory.Bass.StrictDiagramIterateNullTimeSlice
public import Colib.Topology.Prespectrum.ConeDiagramDescent


/-!
# Original finite auxiliary-supported C_Z/F_Z/G_Z Bass stages and whole null transitions

Every stage, transition and r/q map is the unchanged strict Bass iterate of the
actual auxiliary-supported Model diagram and its original seed. The original canonical
localization null is iterated with all its times retained. Its proved seed-time
square supplies the whole finite transition equations. Actual finite Model
excision and the initial cone comparison give stable finite cone descents.
Separately, the constructed original graded seed null gives whole transition
nulls; no finite-stage vanishing or seed-stability premise is assumed.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The same original r transformation at every finite stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassTower.lean:62"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
def boundedAboveFlatCoefficientSupportedOpenBassRestriction (i : ℕ) :
    boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i ⟶
      boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T)

omit [IsOpenImmersion f.left] in
/-- The actual r seed square supplies every unchanged finite transition equation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassTower.lean:70"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
theorem boundedAboveFlatCoefficientSupportedOpenBassRestriction_transition (i : ℕ) :
    boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i ≫
        boundedAboveFlatCoefficientSupportedFullOpenBassTransition f T i =
      boundedAboveFlatCoefficientSupportedOpenBassTransition f T i ≫
        boundedAboveFlatCoefficientSupportedOpenBassRestriction f T (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedOpenBassSeed f T)
      (boundedAboveFlatCoefficientSupportedFullOpenBassSeed f T)
    (boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T)
    (boundedAboveFlatCoefficientSupportedOpenBassSeed_restriction f T) i).symm

omit [IsOpenImmersion f.left] in
/-- Actual finite Model growth supplies excision for the original finite restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassTower.lean:83"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
theorem boundedAboveFlatCoefficientSupportedOpenBassRestriction_coneFiber_isStableEquivalence
    (i : ℕ) (a : Under R) : IsStableEquivalence
      (mappingConeFiberComparison ((boundedAboveFlatCoefficientSupportedOpenBassRestriction f T
        i).app
        a)) :=
  modelDiagramIterateArrow_coneFiber_isStableEquivalence (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedOpenModelFunctor f T)
      (boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T)
    (boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T) i a

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- Original finite G stages of the unchanged raw-image-quotient graded Model diagram. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassTower.lean:95"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
def boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram (i : ℕ) : Under R ⥤
  LoopPrespectrum.{u+1}
  :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T)

/-- Every actual G transition is the unchanged iterated original graded seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTower.lean:101"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
def boundedAboveFlatCoefficientSupportedGradedOpenBassTransition (i : ℕ) :
    boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T i ⟶
      boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedGradedOpenBassSeed f T) i

/-- The same original q transformation at every finite stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTower.lean:108"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
def boundedAboveFlatCoefficientSupportedOpenBassGrading (i : ℕ) :
    boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T i ⟶
      boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T)

/-- The actual q seed square supplies every unchanged finite transition equation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTower.lean:115"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
theorem boundedAboveFlatCoefficientSupportedOpenBassGrading_transition (i : ℕ) :
    boundedAboveFlatCoefficientSupportedOpenBassGrading f T i ≫
      boundedAboveFlatCoefficientSupportedGradedOpenBassTransition f T i =
      boundedAboveFlatCoefficientSupportedFullOpenBassTransition f T i ≫
        boundedAboveFlatCoefficientSupportedOpenBassGrading f T (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedFullOpenBassSeed f T)
      (boundedAboveFlatCoefficientSupportedGradedOpenBassSeed f T)
    (boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T)
    (boundedAboveFlatCoefficientSupportedFullOpenBassSeed_grading f T) i).symm

/-- Iterate precisely the original canonical whole coefficient-natural localization null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTower.lean:127"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
def boundedAboveFlatCoefficientSupportedOpenBassGradingNull (i : ℕ) :
    DiagramNullHomotopy (boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i)
      (boundedAboveFlatCoefficientSupportedOpenBassGrading f T i) :=
  strictDiagramIterateNull (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T) i

/-- The whole finite localization null preserves original seed transitions at every time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTower.lean:134"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
theorem boundedAboveFlatCoefficientSupportedOpenBassGradingNull_transition
    (i : ℕ) (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i).obj a).space m) :
    ((boundedAboveFlatCoefficientSupportedGradedOpenBassTransition f T i).app a).map m
      (((boundedAboveFlatCoefficientSupportedOpenBassGradingNull f T i).homotopy a).level m (s,
        x)) =
    ((boundedAboveFlatCoefficientSupportedOpenBassGradingNull f T (i + 1)).homotopy a).level m
      (s, ((boundedAboveFlatCoefficientSupportedOpenBassTransition f T i).app a).map m x) :=
  (strictDiagramIterateNull_transition (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T)
    (boundedAboveFlatCoefficientSupportedOpenBassSeed f T)
      (boundedAboveFlatCoefficientSupportedGradedOpenBassSeed f T)
    (fun s ↦ boundedAboveFlatCoefficientSupportedOpenGradingNullTimeSlice_seed f T s) i a m s
      x).symm

/-- The actual finite original cone descends along the same complete iterated localization null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTower.lean:148"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
def boundedAboveFlatCoefficientSupportedOpenBassConeComparison (i : ℕ) :
    mappingConeDiagram (boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i) ⟶
      boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T i :=
  mappingConeDescTransformation (boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i)
    (boundedAboveFlatCoefficientSupportedOpenBassGrading f T i)
    (boundedAboveFlatCoefficientSupportedOpenBassGradingNull f T i).homotopy
    (boundedAboveFlatCoefficientSupportedOpenBassGradingNull f T i).naturality

/-- The original finite cone inclusion has precisely the actual q_i face. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTower.lean:157"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
theorem boundedAboveFlatCoefficientSupportedOpenBassConeComparison_inclusion (i : ℕ) (a : Under R) :
    mappingConeInclusion ((boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i).app a) ≫
        (boundedAboveFlatCoefficientSupportedOpenBassConeComparison f T i).app a =
      (boundedAboveFlatCoefficientSupportedOpenBassGrading f T i).app a :=
        mappingConeInclusion_desc _ _
        _

/-- The original graded transition is whole-null through the actual original iterated seed null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTower.lean:164"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
def boundedAboveFlatCoefficientSupportedGradedOpenBassTransitionNull (i : ℕ) (a : Under R) :
    LoopPrespectrum.Homotopy ((boundedAboveFlatCoefficientSupportedGradedOpenBassTransition f T
      i).app a)
      (zeroHom ((boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T i).obj a)
        ((boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T (i + 1)).obj a)) :=
  ((strictDiagramIterateNull (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedGradedOpenBassSeedDiagramNull f T) i).homotopy a).cast (by
      let I := strictDiagramIterate (laurentUnderSquareFunctor R) i
      let B := (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T)
      have hid : (I.map (𝟙 B)).app a = 𝟙 ((I.obj B).obj a) :=
        congrArg (fun η : I.obj B ⟶ I.obj B ↦ η.app a) (I.map_id B)
      exact (congrArg
        (fun g ↦ (I.map (boundedAboveFlatCoefficientSupportedGradedOpenBassSeed f T)).app a ≫ g)
        hid).trans (Category.comp_id _)) rfl

/-- Whole nullity of the original transition proves its signed stable map is zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTower.lean:180"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
theorem boundedAboveFlatCoefficientSupportedGradedOpenBassTransition_stableMap_eq_zero
    (i : ℕ) (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientSupportedGradedOpenBassTransition f T i).app a) = 0 :=
  ((boundedAboveFlatCoefficientSupportedGradedOpenBassTransitionNull f T i a).stableHomotopyMap_eq
    d).trans
    (stableHomotopyMap_zero _ _ d)

variable [QuasiSeparatedSpace Q.left] [CompactSpace T]

/-- Actual finite Model excision propagates the original initial stable cone descent. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTower.lean:191"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
theorem boundedAboveFlatCoefficientSupportedOpenBassConeComparison_isStableEquivalence
    (i : ℕ) (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientSupportedOpenBassConeComparison f T i).app a)
      :=
  modelDiagramIterateCofiberDesc_isStableEquivalence (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedOpenModelFunctor f T)
      (boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T)
    (boundedAboveFlatCoefficientSupportedGradedOpenModelFunctor f T)
    (boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T)
    (boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T)
    (boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T)
    (fun a ↦ boundedAboveFlatCoefficientSupportedOpenGradingConeComparison_isStableEquivalence f T
      a) i a

end AlgebraicGeometry.Scheme.Modules

