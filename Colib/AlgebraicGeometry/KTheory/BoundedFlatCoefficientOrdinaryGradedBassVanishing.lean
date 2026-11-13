/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryGradedLaurentContraction
public import Colib.KTheory.Bass.StrictDiagramIterateNullTimeSlice
public import Colib.KTheory.Bass.ModelDiagramConnectivity
public import Colib.Topology.Prespectrum.TelescopeDiagramMap
public import Colib.Topology.Prespectrum.TelescopeStableRepresentability

/-! # Original ordinary graded Bass vanishing

Nine original declarations are separated only at their complete declaration boundaries.
The same ordinary graded Model, seed, actual telescope and every signed degree are retained.
This file does not assert a restriction cone comparison or localization endpoint.
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

/-- Original finite G stages of the unchanged raw-image-quotient graded Model diagram. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTower.lean:88"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
def boundedAboveFlatCoefficientGradedOpenBassDiagram (i : ℕ) : Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f)

/-- Every actual G transition is the unchanged iterated original graded seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTower.lean:93"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
def boundedAboveFlatCoefficientGradedOpenBassTransition (i : ℕ) :
    boundedAboveFlatCoefficientGradedOpenBassDiagram f i ⟶
      boundedAboveFlatCoefficientGradedOpenBassDiagram f (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientGradedOpenBassSeed f) i

/-- The original graded transition is whole-null through the actual original iterated seed null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTower.lean:152"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
def boundedAboveFlatCoefficientGradedOpenBassTransitionNull (i : ℕ) (a : Under R) :
    LoopPrespectrum.Homotopy ((boundedAboveFlatCoefficientGradedOpenBassTransition f i).app a)
      (zeroHom ((boundedAboveFlatCoefficientGradedOpenBassDiagram f i).obj a)
        ((boundedAboveFlatCoefficientGradedOpenBassDiagram f (i + 1)).obj a)) :=
  ((strictDiagramIterateNull (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientGradedOpenBassSeedDiagramNull f) i).homotopy a).cast (by
      let I := strictDiagramIterate (laurentUnderSquareFunctor R) i
      let B := (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f)
      have hid : (I.map (𝟙 B)).app a = 𝟙 ((I.obj B).obj a) :=
        congrArg (fun η : I.obj B ⟶ I.obj B ↦ η.app a) (I.map_id B)
      exact (congrArg
        (fun g ↦ (I.map (boundedAboveFlatCoefficientGradedOpenBassSeed f)).app a ≫ g)
        hid).trans (Category.comp_id _)) rfl

/-- Whole nullity of the original transition proves its signed stable map is zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTower.lean:168"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
theorem boundedAboveFlatCoefficientGradedOpenBassTransition_stableMap_eq_zero
    (i : ℕ) (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientGradedOpenBassTransition f i).app a) = 0 :=
  ((boundedAboveFlatCoefficientGradedOpenBassTransitionNull f i a).stableHomotopyMap_eq d).trans
    (stableHomotopyMap_zero _ _ d)

/-- Original G completion with the exact original graded seeds and transitions. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTelescope.lean:84"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
def boundedAboveFlatCoefficientGradedOpenBassTelescopeFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedAboveFlatCoefficientGradedOpenBassDiagram f)
    (boundedAboveFlatCoefficientGradedOpenBassTransition f)

/-- Original G stage inclusions with their unchanged initial cylinder faces. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTelescope.lean:98"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
def boundedAboveFlatCoefficientGradedOpenBassTelescopeInclusion (i : ℕ) :
    boundedAboveFlatCoefficientGradedOpenBassDiagram f i ⟶
      boundedAboveFlatCoefficientGradedOpenBassTelescopeFunctor f :=
  Telescope.diagramInclusion (boundedAboveFlatCoefficientGradedOpenBassDiagram f)
    (boundedAboveFlatCoefficientGradedOpenBassTransition f) i

/-- Actual whole transition nulls kill every original G stage-inclusion stable map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTelescope.lean:159"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
theorem boundedAboveFlatCoefficientGradedOpenBassTelescopeInclusion_stableMap_eq_zero
    (i : ℕ) (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientGradedOpenBassTelescopeInclusion f i).app a) = 0 := by
  let E := fun k ↦ (boundedAboveFlatCoefficientGradedOpenBassDiagram f k).obj a
  let τ := fun k ↦ (boundedAboveFlatCoefficientGradedOpenBassTransition f k).app a
  change (stableHomotopyFunctor d).map (Telescope.inclusion E τ i) = 0
  have hi := Telescope.inclusion_transition_stableMap E τ (Nat.le_succ i) d
  rw [Telescope.transition_succ] at hi
  have hz : (stableHomotopyFunctor d).map (τ i) = 0 :=
    boundedAboveFlatCoefficientGradedOpenBassTransition_stableMap_eq_zero f i a d
  exact hi.trans (by rw [hz, CategoryTheory.Limits.zero_comp])

/-- Finite original stable representatives prove G-infinity vanishes in every integer degree. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTelescope.lean:173"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
theorem boundedAboveFlatCoefficientGradedOpenBassTelescope_stableClass_eq_zero
    (a : Under R) (d : ℤ)
    (x : stableHomotopyGroup ((boundedAboveFlatCoefficientGradedOpenBassTelescopeFunctor f).obj a)
      d) :
    x = 0 := by
  let E := fun k ↦ (boundedAboveFlatCoefficientGradedOpenBassDiagram f k).obj a
  let τ := fun k ↦ (boundedAboveFlatCoefficientGradedOpenBassTransition f k).app a
  let : ∀ i n, T1Space ((E i).space n) :=
    fun i n ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientGradedOpenModelFunctor f) a n
  obtain ⟨i, y, hy⟩ := Telescope.exists_stable_representative E τ d x
  have hi := boundedAboveFlatCoefficientGradedOpenBassTelescopeInclusion_stableMap_eq_zero f i a d
  exact hy.symm.trans ((ConcreteCategory.congr_hom hi y).trans rfl)

/-- The actual signed G-infinity groups are subsingletons. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenBassTelescope.lean:187"
  "adaptation" "Original ordinary graded stages, full telescope null and signed vanishing"]
theorem boundedAboveFlatCoefficientGradedOpenBassTelescope_stableGroup_subsingleton
    (a : Under R) (d : ℤ) : Subsingleton (stableHomotopyGroup
      ((boundedAboveFlatCoefficientGradedOpenBassTelescopeFunctor f).obj a) d) :=
  ⟨fun x y ↦ (boundedAboveFlatCoefficientGradedOpenBassTelescope_stableClass_eq_zero f a d x).trans
    (boundedAboveFlatCoefficientGradedOpenBassTelescope_stableClass_eq_zero f a d y).symm⟩

end AlgebraicGeometry.Scheme.Modules
