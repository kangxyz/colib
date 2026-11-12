/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryRowNullHomotopy
public import Colib.Topology.Prespectrum.StrictSquareConeZeroMap

/-! # Literal zero endpoints of the prescribed auxiliary row null

The reduced cone collapses its zero cylinder by its defining basepoint relation.
Only endpoint casts are used; no contraction segment or new time parametrization is appended.
-/
@[expose] public section
noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
open ModelDiagramRowInterchange GeometricSeedCospan
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The original unlooped cone null has a literal zero endpoint. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullEndpoint.lean:30"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullConeNull_at_one (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    (fullConeNull f T i X).at 1 = zeroHom
      (ModelDiagramRowRefinement.source squareFunctor i (fiber f T) X)
      (ModelDiagramRowRefinement.source squareFunctor i (openModel f T) X) := by
  rw [Homotopy.at_one_eq]
  exact StrictSquare.coneMap_eq_zero _ rfl rfl rfl rfl

/-- The complete proper-row null has a literal zero endpoint as well. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullEndpoint.lean:38"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullRowNull_at_one (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    (fullRowNull f T i X).at 1 = zeroHom
      (ModelDiagramRowRefinement.carrier squareFunctor i (fiber f T) X)
      (ModelDiagramRowRefinement.carrier squareFunctor i (openModel f T) X) := by
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
    exact congrArg (fun g => g.map 2 (x s a)) (fullConeNull_at_one f T i X)
  | succ k =>
    change Path
      ((ModelDiagramRowRefinement.source squareFunctor i (fiber f T) X).point (k + 2))
      ((ModelDiagramRowRefinement.source squareFunctor i (fiber f T) X).point (k + 2)) at x
    apply Path.ext
    funext s
    exact congrArg (fun g => g.map (k + 2) (x s)) (fullConeNull_at_one f T i X)

/-- The prescribed row null with its proved literal-zero endpoint, without changing any value. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullEndpoint.lean:65"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def fullRowNullToZero (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  (fullRowNull f T i X).cast (fullRowNull f T i X).at_zero_eq.symm
    ((fullRowNull f T i X).at_one_eq.symm.trans (fullRowNull_at_one f T i X))

/-- Endpoint normalization keeps the complete original row null at the identical time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullEndpoint.lean:70"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullRowNullToZero_level (i : ℕ) (X : Scheme.{u}ᵒᵖ) (n : ℕ) :
    (fullRowNullToZero f T i X).level n = (fullRowNull f T i X).level n := rfl

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
