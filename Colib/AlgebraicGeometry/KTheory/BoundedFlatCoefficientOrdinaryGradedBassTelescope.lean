/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryGradedBassTower
public import Colib.Topology.Prespectrum.TelescopeDiagramMap
public import Colib.Topology.Prespectrum.TelescopeConeDescentStable

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

/-- Original coefficient-natural q-infinity retaining all finite grading components. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTelescope.lean:89"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
def boundedAboveFlatCoefficientOpenBassTelescopeGrading :
    boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor f ⟶
      boundedAboveFlatCoefficientGradedOpenBassTelescopeFunctor f :=
  Telescope.diagramMap (boundedAboveFlatCoefficientFullOpenBassDiagram f)
    (boundedAboveFlatCoefficientGradedOpenBassDiagram f)
      (boundedAboveFlatCoefficientFullOpenBassTransition f)
    (boundedAboveFlatCoefficientGradedOpenBassTransition f)
      (boundedAboveFlatCoefficientOpenBassGrading f)
    (boundedAboveFlatCoefficientOpenBassGrading_transition f)

/-- The original grading retains every finite inclusion face. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTelescope.lean:105"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
theorem boundedAboveFlatCoefficientOpenBassTelescopeInclusion_grading (i : ℕ) :
    boundedAboveFlatCoefficientFullOpenBassTelescopeInclusion f i ≫
        boundedAboveFlatCoefficientOpenBassTelescopeGrading f =
      boundedAboveFlatCoefficientOpenBassGrading f i ≫
        boundedAboveFlatCoefficientGradedOpenBassTelescopeInclusion f i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- The same complete finite localization nulls define the original coefficient telescope null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTelescope.lean:113"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
def boundedAboveFlatCoefficientOpenBassTelescopeGradingNull :
    DiagramNullHomotopy (boundedAboveFlatCoefficientOpenBassTelescopeRestriction f)
      (boundedAboveFlatCoefficientOpenBassTelescopeGrading f) where
  homotopy a := Telescope.mapNullHomotopy
    (fun i ↦ (boundedAboveFlatCoefficientOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientOpenBassTransition f i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientFullOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientFullOpenBassTransition f i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientGradedOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientGradedOpenBassTransition f i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientOpenBassRestriction f i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientOpenBassGrading f i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedAboveFlatCoefficientOpenBassRestriction_transition
      f i))
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedAboveFlatCoefficientOpenBassGrading_transition f i))
    (fun i ↦ (boundedAboveFlatCoefficientOpenBassGradingNull f i).homotopy a)
    (fun i m s x ↦ boundedAboveFlatCoefficientOpenBassGradingNull_transition f i a m s x)
  naturality {a b} g m s x := by
    induction x using Quot.inductionOn with
    | h z =>
      change Telescope.cylinder
          (fun i ↦ (boundedAboveFlatCoefficientGradedOpenBassDiagram f i).obj b)
          (fun i ↦ (boundedAboveFlatCoefficientGradedOpenBassTransition f i).app b) m z.1
          (z.2.1, ((boundedAboveFlatCoefficientGradedOpenBassDiagram f z.1).map g).map m
            (((boundedAboveFlatCoefficientOpenBassGradingNull f z.1).homotopy a).level m (s,
              z.2.2))) =
        Telescope.cylinder
          (fun i ↦ (boundedAboveFlatCoefficientGradedOpenBassDiagram f i).obj b)
          (fun i ↦ (boundedAboveFlatCoefficientGradedOpenBassTransition f i).app b) m z.1
          (z.2.1, ((boundedAboveFlatCoefficientOpenBassGradingNull f z.1).homotopy b).level m
            (s, ((boundedAboveFlatCoefficientOpenBassDiagram f z.1).map g).map m z.2.2))
      exact congrArg (fun y ↦ Telescope.cylinder
        (fun i ↦ (boundedAboveFlatCoefficientGradedOpenBassDiagram f i).obj b)
        (fun i ↦ (boundedAboveFlatCoefficientGradedOpenBassTransition f i).app b) m z.1 (z.2.1, y))
        ((boundedAboveFlatCoefficientOpenBassGradingNull f z.1).naturality g m s z.2.2)

/-- The canonical null time and original telescope height stay independent. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTelescope.lean:148"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
theorem boundedAboveFlatCoefficientOpenBassTelescopeGradingNull_cylinder
    (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatCoefficientOpenBassDiagram f i).obj a).space m) :
    ((boundedAboveFlatCoefficientOpenBassTelescopeGradingNull f).homotopy a).level m
      (s, Telescope.cylinder (fun k ↦ (boundedAboveFlatCoefficientOpenBassDiagram f k).obj a)
        (fun k ↦ (boundedAboveFlatCoefficientOpenBassTransition f k).app a) m i (t, x)) =
    Telescope.cylinder (fun k ↦ (boundedAboveFlatCoefficientGradedOpenBassDiagram f k).obj a)
      (fun k ↦ (boundedAboveFlatCoefficientGradedOpenBassTransition f k).app a) m i
        (t, ((boundedAboveFlatCoefficientOpenBassGradingNull f i).homotopy a).level m (s, x)) := rfl

/-- The original telescope cone descends with precisely the same complete N-infinity. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTelescope.lean:194"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
def boundedAboveFlatCoefficientOpenBassTelescopeConeComparison :
    mappingConeDiagram (boundedAboveFlatCoefficientOpenBassTelescopeRestriction f) ⟶
      boundedAboveFlatCoefficientGradedOpenBassTelescopeFunctor f :=
  mappingConeDescTransformation (boundedAboveFlatCoefficientOpenBassTelescopeRestriction f)
    (boundedAboveFlatCoefficientOpenBassTelescopeGrading f)
    (boundedAboveFlatCoefficientOpenBassTelescopeGradingNull f).homotopy
    (boundedAboveFlatCoefficientOpenBassTelescopeGradingNull f).naturality

/-- The original telescope cone inclusion has exactly q-infinity as its face. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTelescope.lean:203"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
theorem boundedAboveFlatCoefficientOpenBassTelescopeConeComparison_inclusion (a : Under R) :
    mappingConeInclusion ((boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app a) ≫
        (boundedAboveFlatCoefficientOpenBassTelescopeConeComparison f).app a =
      (boundedAboveFlatCoefficientOpenBassTelescopeGrading f).app a := mappingConeInclusion_desc _
        _ _

variable [QuasiSeparatedSpace Q.left]

/-- Actual finite cone stability passes to the same original telescope descent. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTelescope.lean:231"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
theorem boundedAboveFlatCoefficientOpenBassTelescopeConeComparison_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientOpenBassTelescopeConeComparison f).app a) := by
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientOpenBassDiagram f i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientOpenModelFunctor f) a m
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientFullOpenBassDiagram f i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientFullOpenModelFunctor f) a m
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientGradedOpenBassDiagram f i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientGradedOpenModelFunctor f) a m
  exact Telescope.coneDesc_isStableEquivalence
    (fun i ↦ (boundedAboveFlatCoefficientOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientOpenBassTransition f i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientFullOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientFullOpenBassTransition f i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientGradedOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientGradedOpenBassTransition f i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientOpenBassRestriction f i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientOpenBassGrading f i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedAboveFlatCoefficientOpenBassRestriction_transition
      f i))
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedAboveFlatCoefficientOpenBassGrading_transition f i))
    (fun i ↦ (boundedAboveFlatCoefficientOpenBassGradingNull f i).homotopy a)
    (fun i m s x ↦ boundedAboveFlatCoefficientOpenBassGradingNull_transition f i a m s x)
    (fun i ↦ boundedAboveFlatCoefficientOpenBassConeComparison_isStableEquivalence f i a)

end AlgebraicGeometry.Scheme.Modules
