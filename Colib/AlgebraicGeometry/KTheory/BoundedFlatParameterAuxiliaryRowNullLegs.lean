/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryRowNullBackward
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryRowPresentation
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeIndexTransport

/-! # The complete auxiliary null preserves both genuine row-presentation legs -/
@[expose] public section
noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Topology.LoopPrespectrum KTheory.Bass CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
open GeometricSeedCospan ModelRowZigzagSequentialization
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The original cone null begins at the two actual input cone maps composed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullLegs.lean:28"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullConeNull_at_zero (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    (fullConeNull f T i X).at 0 =
      (ModelDiagramRowRefinement.inputSourceMap squareFunctor i (enlargement f T)).app X ≫
      (ModelDiagramRowRefinement.inputSourceMap squareFunctor i (restriction f T)).app X := by
  rw [Homotopy.at_zero_eq]
  exact congrArg (fun η => η.app X)
    (GeometricConeInterchange.coneFunctor.map_comp
      ((strictDiagramIterate squareFunctor i).map (firstMap f T))
      ((strictDiagramIterate squareFunctor i).map (secondMap f T)))

/-- The refined row null begins at the original two row input maps composed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullLegs.lean:39"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullRowNull_at_zero (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    (fullRowNull f T i X).at 0 =
      ModelDiagramRowRefinement.inputMap squareFunctor i (enlargement f T) X ≫
      ModelDiagramRowRefinement.inputMap squareFunctor i (restriction f T) X := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  cases n with
  | zero =>
    change Path
      (Path.refl ((ModelDiagramRowRefinement.source squareFunctor i (fiber f T) X).point 2))
      (Path.refl ((ModelDiagramRowRefinement.source squareFunctor i (fiber f T) X).point 2)) at x
    apply Path.ext
    funext s
    apply Path.ext
    funext a
    exact congrArg (fun g => g.map 2 (x s a)) (fullConeNull_at_zero f T i X)
  | succ k =>
    change Path
      ((ModelDiagramRowRefinement.source squareFunctor i (fiber f T) X).point (k + 2))
      ((ModelDiagramRowRefinement.source squareFunctor i (fiber f T) X).point (k + 2)) at x
    apply Path.ext
    funext s
    exact congrArg (fun g => g.map (k + 2) (x s)) (fullConeNull_at_zero f T i X)

/-- The target null has exactly the actual composite presentation-input endpoint. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullLegs.lean:66"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullTargetNull_at_zero (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    (fullTargetNull f T i X).at 0 =
      SchemeModelRowSeed.targetInput (fiber f T) (ambient T) (enlargement f T) i X ≫
      SchemeModelRowSeed.targetInput (ambient T) (openModel f T) (restriction f T) i X := by
  rw [fullTargetNull, Homotopy.parameterLooping_at, fullRowNull_at_zero]
  exact parameterLoopingFunctor.map_comp _ _

/-- The target null ends at literal zero with its independent loop coordinate unchanged. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullLegs.lean:74"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullTargetNull_at_one (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    (fullTargetNull f T i X).at 1 = zeroHom
      (target squareFunctor (fiber f T) X i) (target squareFunctor (openModel f T) X i) := by
  rw [fullTargetNull, Homotopy.parameterLooping_at, fullRowNull_at_one]
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  rfl

/-- The original target null, with both actual presentation-input endpoints made explicit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullLegs.lean:87"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def fullTargetInputNull (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  (fullTargetNull f T i X).cast
    ((fullTargetNull f T i X).at_zero_eq.symm.trans (fullTargetNull_at_zero f T i X))
    ((fullTargetNull f T i X).at_one_eq.symm.trans (fullTargetNull_at_one f T i X))

private theorem pasteForwardSquare {C : Type*} [Category C] {A B D A' B' D' : C}
    (a : A ⟶ D) (b : B ⟶ D) (step : A ⟶ B)
    (a' : A' ⟶ D') (b' : B' ⟶ D') (step' : A' ⟶ B')
    (d : A ⟶ A') (e : B ⟶ B') (v : D ⟶ D')
    (ha : a = step ≫ b) (ha' : a' = step' ≫ b')
    (hb : b ≫ v = e ≫ b') (hstep : step ≫ e = d ≫ step') :
    a ≫ v = d ≫ a' := by
  rw [ha, ha', Category.assoc, hb, ← Category.assoc, hstep, Category.assoc]

/-- The unchanged auxiliary null preserves every original current transition. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullLegs.lean:102"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullNull_current_at (i : ℕ) (X : Scheme.{u}ᵒᵖ) (r : unitInterval) :
    ((SchemeNaturalSeed.currentTransition (fiberAction f T) i).app X) ≫
        ((strictDiagramIterateNull squareFunctor (fullNull f T) (i + 1)).homotopy X).at r =
      ((strictDiagramIterateNull squareFunctor (fullNull f T) i).homotopy X).at r ≫
        ((SchemeNaturalSeed.currentTransition (openAction f T) i).app X) := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact (SchemeNaturalSeed.currentNull_transition (fiberAction f T) (openAction f T)
    (firstMap f T) (secondMap f T) (fullNull f T) (timeSlice_equivariant f T) i X n r x).symm

/-- Independent forward seeds retain the complete original auxiliary null at every time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullLegs.lean:115"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullTargetNull_forward_at (i : ℕ) (X : Scheme.{u}ᵒᵖ) (r : unitInterval) :
    SchemeModelRowSeed.forward (fiber f T) (supportedUnit (unionOpen f T).ι)
        (supportedUnit_naturality (unionOpen f T).ι) i X ≫ (fullTargetNull f T i X).at r =
      ((strictDiagramIterateNull squareFunctor (fullNull f T) i).homotopy X).at r ≫
        SchemeModelRowSeed.forward (openModel f T) (supportedUnit (inverseOpen f T).ι)
          (supportedUnit_naturality (inverseOpen f T).ι) i X :=
  pasteForwardSquare _ _ _ _ _ _ _ _ _
    (SchemeModelRowSeed.forward_eq_current (fiber f T) (supportedUnit (unionOpen f T).ι)
      (supportedUnit_naturality (unionOpen f T).ι) i X)
    (SchemeModelRowSeed.forward_eq_current (openModel f T) (supportedUnit (inverseOpen f T).ι)
      (supportedUnit_naturality (inverseOpen f T).ι) i X)
    (fullTargetNull_backward_at f T i X r).symm (fullNull_current_at f T i X r)

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
