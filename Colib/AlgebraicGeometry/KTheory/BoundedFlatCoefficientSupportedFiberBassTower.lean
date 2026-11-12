/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFiberBassSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenBassStages
public import Colib.KTheory.Bass.ModelDiagramIterateCofiberPreservation
public import Colib.KTheory.Bass.StrictDiagramIterateNullTimeSlice


/-!
# Original intersection-support inclusion and localization at every Bass stage

Finite fiber and auxiliary ambient stages are literal strict Bass iterates of
their actual native Model diagrams. The original inclusion, identity weakness
change and complete supported null are iterated unchanged. Every null-time
transition equation follows from the actual original time-slice seed square.
Native initial cone stability and genuine finite Model excision pass to each
same original finite cone, without any stabilization or localization premise.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory Topology AlgebraicGeometry Topology.LoopPrespectrum
open KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Literal finite Bass iterates of the actual native supported coefficient row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTower.lean:35"
  "adaptation" "Actual auxiliary fiber Bass stages, same whole null and finite cone stability"]
def boundedAboveFlatCoefficientSupportedFiberBassDiagram (i : ℕ) : Under R ⥤ LoopPrespectrum.{u+1}
  :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedAboveFlatCoefficientSupportedFiberPrespectrumFunctor f T)

/-- Literal finite Bass iterates of the original native fine ambient row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTower.lean:40"
  "adaptation" "Actual auxiliary fiber Bass stages, same whole null and finite cone stability"]
def boundedAboveFlatCoefficientSupportedAmbientBassDiagram (i : ℕ) :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedAboveFlatCoefficientSupportedAmbientPrespectrumFunctor T)

/-- The unchanged finite supported transition is the original iterated supported seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTower.lean:46"
  "adaptation" "Actual auxiliary fiber Bass stages, same whole null and finite cone stability"]
def boundedAboveFlatCoefficientSupportedFiberBassTransition (i : ℕ) :
    boundedAboveFlatCoefficientSupportedFiberBassDiagram f T i ⟶
      boundedAboveFlatCoefficientSupportedFiberBassDiagram f T (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedFiberBassSeed f T) i

/-- The unchanged finite ambient transition is the original iterated ambient seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTower.lean:53"
  "adaptation" "Actual auxiliary fiber Bass stages, same whole null and finite cone stability"]
def boundedAboveFlatCoefficientSupportedAmbientBassTransition (i : ℕ) :
    boundedAboveFlatCoefficientSupportedAmbientBassDiagram T i ⟶
      boundedAboveFlatCoefficientSupportedAmbientBassDiagram T (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedAmbientBassSeed T) i

/-- The original supported inclusion at every unchanged finite Bass stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTower.lean:60"
  "adaptation" "Actual auxiliary fiber Bass stages, same whole null and finite cone stability"]
def boundedAboveFlatCoefficientSupportedFiberBassForget (i : ℕ) :
    boundedAboveFlatCoefficientSupportedFiberBassDiagram f T i ⟶
      boundedAboveFlatCoefficientSupportedAmbientBassDiagram T i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T)

/-- The original ambient change to coarse relative-open weakness at every finite stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTower.lean:67"
  "adaptation" "Actual auxiliary fiber Bass stages, same whole null and finite cone stability"]
def boundedAboveFlatCoefficientSupportedAmbientBassOpen (i : ℕ) :
    boundedAboveFlatCoefficientSupportedAmbientBassDiagram T i ⟶
      boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T)

/-- The actual original supported inclusion commutes with every unchanged seed transition. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTower.lean:74"
  "adaptation" "Actual auxiliary fiber Bass stages, same whole null and finite cone stability"]
theorem boundedAboveFlatCoefficientSupportedFiberBassForget_transition (i : ℕ) :
    boundedAboveFlatCoefficientSupportedFiberBassForget f T i ≫
        boundedAboveFlatCoefficientSupportedAmbientBassTransition T i =
      boundedAboveFlatCoefficientSupportedFiberBassTransition f T i ≫
        boundedAboveFlatCoefficientSupportedFiberBassForget f T (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedFiberBassSeed f T)
      (boundedAboveFlatCoefficientSupportedAmbientBassSeed T)
    (boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T)
    (boundedAboveFlatCoefficientSupportedFiberBassSeed_forget f T) i).symm

omit [IsOpenImmersion f.left] in
/-- The same original fine-to-coarse map commutes with every actual finite transition. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTower.lean:87"
  "adaptation" "Actual auxiliary fiber Bass stages, same whole null and finite cone stability"]
theorem boundedAboveFlatCoefficientSupportedAmbientBassOpen_transition (i : ℕ) :
    boundedAboveFlatCoefficientSupportedAmbientBassOpen f T i ≫
      boundedAboveFlatCoefficientSupportedOpenBassTransition f T i =
      boundedAboveFlatCoefficientSupportedAmbientBassTransition T i ≫
        boundedAboveFlatCoefficientSupportedAmbientBassOpen f T (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedAmbientBassSeed T)
      (boundedAboveFlatCoefficientSupportedOpenBassSeed
      f T)
    (boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T)
    (boundedAboveFlatCoefficientSupportedAmbientBassSeed_open f T) i).symm

/-- Iterate precisely the same original coefficient-natural whole supported localization null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTower.lean:99"
  "adaptation" "Actual auxiliary fiber Bass stages, same whole null and finite cone stability"]
def boundedAboveFlatCoefficientSupportedFiberBassOpenNull (i : ℕ) :
    DiagramNullHomotopy (boundedAboveFlatCoefficientSupportedFiberBassForget f T i)
      (boundedAboveFlatCoefficientSupportedAmbientBassOpen f T i) :=
  strictDiagramIterateNull (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T) i

/-- All original null times preserve every unchanged finite supported/open transition. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTower.lean:106"
  "adaptation" "Actual auxiliary fiber Bass stages, same whole null and finite cone stability"]
theorem boundedAboveFlatCoefficientSupportedFiberBassOpenNull_transition
    (i : ℕ) (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedFiberBassDiagram f T i).obj a).space m) :
    ((boundedAboveFlatCoefficientSupportedOpenBassTransition f T i).app a).map m
        (((boundedAboveFlatCoefficientSupportedFiberBassOpenNull f T i).homotopy a).level m (s,
          x)) =
      ((boundedAboveFlatCoefficientSupportedFiberBassOpenNull f T (i + 1)).homotopy a).level m
        (s, ((boundedAboveFlatCoefficientSupportedFiberBassTransition f T i).app a).map m x) :=
  (strictDiagramIterateNull_transition (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T)
    (boundedAboveFlatCoefficientSupportedFiberBassSeed f T)
      (boundedAboveFlatCoefficientSupportedOpenBassSeed
      f T)
    (fun s ↦ boundedAboveFlatCoefficientSupportedFiberOpenNullTimeSlice_seed f T s) i a m s x).symm

/-- Actual finite cone descent along the unchanged complete iterated supported localization null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTower.lean:120"
  "adaptation" "Actual auxiliary fiber Bass stages, same whole null and finite cone stability"]
def boundedAboveFlatCoefficientSupportedFiberBassOpenConeMap (i : ℕ) :
    mappingConeDiagram (boundedAboveFlatCoefficientSupportedFiberBassForget f T i) ⟶
      boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i :=
  mappingConeDescTransformation (boundedAboveFlatCoefficientSupportedFiberBassForget f T i)
    (boundedAboveFlatCoefficientSupportedAmbientBassOpen f T i)
    (boundedAboveFlatCoefficientSupportedFiberBassOpenNull f T i).homotopy
    (boundedAboveFlatCoefficientSupportedFiberBassOpenNull f T i).naturality

/-- Every original ambient inclusion face is exactly the original finite fine-to-coarse map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTower.lean:129"
  "adaptation" "Actual auxiliary fiber Bass stages, same whole null and finite cone stability"]
theorem boundedAboveFlatCoefficientSupportedFiberBassOpenConeMap_inclusion (i : ℕ) (a : Under R) :
    mappingConeInclusion ((boundedAboveFlatCoefficientSupportedFiberBassForget f T i).app a) ≫
        (boundedAboveFlatCoefficientSupportedFiberBassOpenConeMap f T i).app a =
      (boundedAboveFlatCoefficientSupportedAmbientBassOpen f T i).app a :=
        mappingConeInclusion_desc _ _
        _

/-- Actual finite Model excision propagates stability of the original initial support cone. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTower.lean:136"
  "adaptation" "Actual auxiliary fiber Bass stages, same whole null and finite cone stability"]
theorem boundedAboveFlatCoefficientSupportedFiberBassOpenConeMap_isStableEquivalence
    (i : ℕ) (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientSupportedFiberBassOpenConeMap f T i).app a) :=
  modelDiagramIterateCofiberDesc_isStableEquivalence (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedFiberModelFunctor f T)
      (boundedAboveFlatCoefficientSupportedAmbientModelFunctor T)
    (boundedAboveFlatCoefficientSupportedOpenModelFunctor f T)
    (boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T)
    (boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T)
    (boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T)
    (fun a ↦ boundedAboveFlatCoefficientSupportedFiberOpenConeComparison_isStableEquivalence f T
      a) i a

/-- Genuine finite Model growth supplies signed excision for the original supported inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTower.lean:149"
  "adaptation" "Actual auxiliary fiber Bass stages, same whole null and finite cone stability"]
theorem boundedAboveFlatCoefficientSupportedFiberBassForget_coneFiber_isStableEquivalence
    (i : ℕ) (a : Under R) :
    IsStableEquivalence (mappingConeFiberComparison
      ((boundedAboveFlatCoefficientSupportedFiberBassForget f T i).app a)) :=
  modelDiagramIterateArrow_coneFiber_isStableEquivalence (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedFiberModelFunctor f T)
      (boundedAboveFlatCoefficientSupportedAmbientModelFunctor T)
    (boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T) i a


end AlgebraicGeometry.Scheme.Modules
