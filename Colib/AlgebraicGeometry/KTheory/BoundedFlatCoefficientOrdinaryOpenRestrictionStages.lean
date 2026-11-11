/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOpenRestrictionSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenBassStages
public import Colib.KTheory.Bass.ModelDiagramIterateCofiberPreservation
public import Colib.KTheory.Bass.StrictDiagramMap
public import Colib.Topology.Prespectrum.TelescopeDiagramMap
public import Colib.Topology.Prespectrum.TelescopeConeDescentStable
/-! # Ordinary finite and completed restriction with actual cone-to-fiber comparison

This selected original scope does not assert the restriction itself is stable.
That further conclusion needs the actual ordinary graded row and its contraction.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology AlgebraicGeometry Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
/-- The same original r transformation at every finite stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTower.lean:61"
  "adaptation" "Original actual ordinary restriction on finite stages and telescope"]
def boundedAboveFlatCoefficientOpenBassRestriction (i : ℕ) :
    boundedAboveFlatCoefficientOpenBassDiagram f i ⟶
      boundedAboveFlatCoefficientFullOpenBassDiagram f i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f)


/-- The actual r seed square supplies every unchanged finite transition equation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTower.lean:67"
  "adaptation" "Original actual ordinary restriction on finite stages and telescope"]
theorem boundedAboveFlatCoefficientOpenBassRestriction_transition (i : ℕ) :
    boundedAboveFlatCoefficientOpenBassRestriction f i ≫
        boundedAboveFlatCoefficientFullOpenBassTransition f i =
      boundedAboveFlatCoefficientOpenBassTransition f i ≫
        boundedAboveFlatCoefficientOpenBassRestriction f (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientOpenBassSeed f) (boundedAboveFlatCoefficientFullOpenBassSeed f)
    (boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f)
    (boundedAboveFlatCoefficientOpenBassSeed_restriction f) i).symm


/-- Actual finite Model growth supplies excision for the original finite restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTower.lean:78"
  "adaptation" "Original actual ordinary restriction on finite stages and telescope"]
theorem boundedAboveFlatCoefficientOpenBassRestriction_coneFiber_isStableEquivalence
    (i : ℕ) (a : Under R) : IsStableEquivalence
      (mappingConeFiberComparison ((boundedAboveFlatCoefficientOpenBassRestriction f i).app a)) :=
  modelDiagramIterateArrow_coneFiber_isStableEquivalence (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientOpenModelFunctor f)
      (boundedAboveFlatCoefficientFullOpenModelFunctor f)
    (boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f) i a

/-- Original coefficient-natural r-infinity retaining all finite restriction components. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTelescope.lean:52"
  "adaptation" "Original actual ordinary restriction on finite stages and telescope"]
def boundedAboveFlatCoefficientOpenBassTelescopeRestriction :
    boundedAboveFlatCoefficientOpenBassTelescopeFunctor f ⟶
      boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor f :=
  Telescope.diagramMap (boundedAboveFlatCoefficientOpenBassDiagram f)
    (boundedAboveFlatCoefficientFullOpenBassDiagram f)
      (boundedAboveFlatCoefficientOpenBassTransition f)
    (boundedAboveFlatCoefficientFullOpenBassTransition f)
      (boundedAboveFlatCoefficientOpenBassRestriction f)
    (boundedAboveFlatCoefficientOpenBassRestriction_transition f)


/-- The original restriction retains every finite inclusion face. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTelescope.lean:74"
  "adaptation" "Original actual ordinary restriction on finite stages and telescope"]
theorem boundedAboveFlatCoefficientOpenBassTelescopeInclusion_restriction (i : ℕ) :
    boundedAboveFlatCoefficientOpenBassTelescopeInclusion f i ≫
        boundedAboveFlatCoefficientOpenBassTelescopeRestriction f =
      boundedAboveFlatCoefficientOpenBassRestriction f i ≫
        boundedAboveFlatCoefficientFullOpenBassTelescopeInclusion f i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- Genuine finite Model excision supplies the original telescope cone-to-fiber comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTelescope.lean:210"
  "adaptation" "Original actual ordinary restriction on finite stages and telescope"]
theorem boundedAboveFlatCoefficientOpenBassTelescopeRestriction_coneFiber_isStableEquivalence
    (a : Under R) : IsStableEquivalence (mappingConeFiberComparison
      ((boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app a)) := by
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientOpenBassDiagram f i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientOpenModelFunctor f) a m
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientFullOpenBassDiagram f i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientFullOpenModelFunctor f) a m
  exact Telescope.coneFiberComparison_isStableEquivalence
    (fun i ↦ (boundedAboveFlatCoefficientOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientOpenBassTransition f i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientFullOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientFullOpenBassTransition f i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientOpenBassRestriction f i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedAboveFlatCoefficientOpenBassRestriction_transition
      f i))
    (fun i ↦ boundedAboveFlatCoefficientOpenBassRestriction_coneFiber_isStableEquivalence f i a)

end AlgebraicGeometry.Scheme.Modules
