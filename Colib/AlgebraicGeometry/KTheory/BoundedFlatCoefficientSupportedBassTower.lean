/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinarySupportedBassSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenBassStages
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportConeStable
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAmbientBassTelescope
public import Colib.KTheory.Bass.ModelDiagramIterateCofiberPreservation
public import Colib.KTheory.Bass.StrictDiagramIterateNullTimeSlice
/-! # Original finite ordinary supported Bass tower

The native ambient stages are reused. The actual whole-null time slices retain their strict
transition equation; finite cone and cone-fiber stability use the original Model excision.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- Literal finite Bass iterates of the actual native supported coefficient row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTower.lean:34"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
def boundedAboveFlatCoefficientSupportedBassDiagram (i : ℕ) : Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedAboveFlatCoefficientSupportedPrespectrumFunctor f)

/-- The unchanged finite supported transition is the original iterated supported seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTower.lean:45"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
def boundedAboveFlatCoefficientSupportedBassTransition (i : ℕ) :
    boundedAboveFlatCoefficientSupportedBassDiagram f i ⟶
      boundedAboveFlatCoefficientSupportedBassDiagram f (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedBassSeed f) i

/-- The original supported inclusion at every unchanged finite Bass stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTower.lean:58"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
def boundedAboveFlatCoefficientSupportedBassForget (i : ℕ) :
    boundedAboveFlatCoefficientSupportedBassDiagram f i ⟶
      boundedAboveFlatCoefficientAmbientBassDiagram Q i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f)

/-- The original ambient change to coarse relative-open weakness at every finite stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTower.lean:64"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
def boundedAboveFlatCoefficientAmbientBassOpen (i : ℕ) :
    boundedAboveFlatCoefficientAmbientBassDiagram Q i ⟶ boundedAboveFlatCoefficientOpenBassDiagram
      f i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f)

/-- The actual original supported inclusion commutes with every unchanged seed transition. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTower.lean:70"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
theorem boundedAboveFlatCoefficientSupportedBassForget_transition (i : ℕ) :
    boundedAboveFlatCoefficientSupportedBassForget f i ≫
        boundedAboveFlatCoefficientAmbientBassTransition Q i =
      boundedAboveFlatCoefficientSupportedBassTransition f i ≫
        boundedAboveFlatCoefficientSupportedBassForget f (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedBassSeed f) (boundedAboveFlatCoefficientAmbientBassSeed Q)
    (boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f)
    (boundedAboveFlatCoefficientSupportedBassSeed_forget f) i).symm

/-- The same original fine-to-coarse map commutes with every actual finite transition. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTower.lean:81"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
theorem boundedAboveFlatCoefficientAmbientBassOpen_transition (i : ℕ) :
    boundedAboveFlatCoefficientAmbientBassOpen f i ≫ boundedAboveFlatCoefficientOpenBassTransition
      f i =
      boundedAboveFlatCoefficientAmbientBassTransition Q i ≫
        boundedAboveFlatCoefficientAmbientBassOpen f (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientAmbientBassSeed Q) (boundedAboveFlatCoefficientOpenBassSeed f)
    (boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f)
    (boundedAboveFlatCoefficientAmbientBassSeed_open f) i).symm

/-- Iterate precisely the same original coefficient-natural whole supported localization null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTower.lean:91"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
def boundedAboveFlatCoefficientSupportedBassOpenNull (i : ℕ) :
    DiagramNullHomotopy (boundedAboveFlatCoefficientSupportedBassForget f i)
      (boundedAboveFlatCoefficientAmbientBassOpen f i) :=
  strictDiagramIterateNull (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedOpenDiagramNull f) i

/-- All original null times preserve every unchanged finite supported/open transition. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTower.lean:98"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
theorem boundedAboveFlatCoefficientSupportedBassOpenNull_transition
    (i : ℕ) (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedBassDiagram f i).obj a).space m) :
    ((boundedAboveFlatCoefficientOpenBassTransition f i).app a).map m
        (((boundedAboveFlatCoefficientSupportedBassOpenNull f i).homotopy a).level m (s, x)) =
      ((boundedAboveFlatCoefficientSupportedBassOpenNull f (i + 1)).homotopy a).level m
        (s, ((boundedAboveFlatCoefficientSupportedBassTransition f i).app a).map m x) :=
  (strictDiagramIterateNull_transition (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedOpenDiagramNull f)
    (boundedAboveFlatCoefficientSupportedBassSeed f) (boundedAboveFlatCoefficientOpenBassSeed f)
    (fun s ↦ boundedAboveFlatCoefficientSupportedOpenNullTimeSlice_seed f s) i a m s x).symm

/-- Actual finite cone descent along the unchanged complete iterated supported localization null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTower.lean:111"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
def boundedAboveFlatCoefficientSupportedBassOpenConeMap (i : ℕ) :
    mappingConeDiagram (boundedAboveFlatCoefficientSupportedBassForget f i) ⟶
      boundedAboveFlatCoefficientOpenBassDiagram f i :=
  mappingConeDescTransformation (boundedAboveFlatCoefficientSupportedBassForget f i)
    (boundedAboveFlatCoefficientAmbientBassOpen f i)
    (boundedAboveFlatCoefficientSupportedBassOpenNull f i).homotopy
    (boundedAboveFlatCoefficientSupportedBassOpenNull f i).naturality

/-- Every original ambient inclusion face is exactly the original finite fine-to-coarse map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTower.lean:120"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
theorem boundedAboveFlatCoefficientSupportedBassOpenConeMap_inclusion (i : ℕ) (a : Under R) :
    mappingConeInclusion ((boundedAboveFlatCoefficientSupportedBassForget f i).app a) ≫
        (boundedAboveFlatCoefficientSupportedBassOpenConeMap f i).app a =
      (boundedAboveFlatCoefficientAmbientBassOpen f i).app a := mappingConeInclusion_desc _ _ _

/-- Actual finite Model excision propagates stability of the original initial support cone. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTower.lean:126"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
theorem boundedAboveFlatCoefficientSupportedBassOpenConeMap_isStableEquivalence
    (i : ℕ) (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientSupportedBassOpenConeMap f i).app a) :=
  modelDiagramIterateCofiberDesc_isStableEquivalence (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedModelFunctor f)
      (boundedAboveFlatCoefficientSectionModelRow Q)
    (boundedAboveFlatCoefficientOpenModelFunctor f)
    (boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f)
    (boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f)
    (boundedAboveFlatCoefficientSupportedOpenDiagramNull f)
    (fun a ↦ boundedAboveFlatCoefficientSupportedOpenConeComparison_isStableEquivalence f a) i a

/-- Genuine finite Model growth supplies signed excision for the original supported inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTower.lean:138"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
theorem boundedAboveFlatCoefficientSupportedBassForget_coneFiber_isStableEquivalence
    (i : ℕ) (a : Under R) :
    IsStableEquivalence (mappingConeFiberComparison
      ((boundedAboveFlatCoefficientSupportedBassForget f i).app a)) :=
  modelDiagramIterateArrow_coneFiber_isStableEquivalence (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedModelFunctor f)
      (boundedAboveFlatCoefficientSectionModelRow Q)
    (boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f) i a

end AlgebraicGeometry.Scheme.Modules
