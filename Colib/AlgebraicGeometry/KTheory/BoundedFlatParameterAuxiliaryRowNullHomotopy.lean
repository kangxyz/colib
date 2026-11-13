/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryRowNull
public import Colib.Topology.Prespectrum.RowRefinementHomotopy

/-! # The original auxiliary null on the genuine finite row carriers

The entire cone homotopy is retained at its original time. Its endpoint row equations are
obtained by evaluating the proved whole-time equation, rather than assumed independently.
-/
@[expose] public section
noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
/-- Refine a whole row-compatible homotopy, deriving both endpoint laws from its time slices. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullHomotopy.lean:27"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def refineWholeRowHomotopy {E F : Topology.LoopPrespectrum.{u}}
    (qE : ∀ k, C(E.space (k + 3), E.space (k + 3)))
    (qF : ∀ k, C(F.space (k + 3), F.space (k + 3)))
    (hE : ∀ k, qE k (E.point (k + 3)) = E.point (k + 3))
    (hF : ∀ k, qF k (F.point (k + 3)) = F.point (k + 3))
    {a b : E ⟶ F} (H : Topology.LoopPrespectrum.Homotopy a b)
    (hH : ∀ k t x, qF k (H.level (k + 3) (t, x)) =
      H.level (k + 3) (t, qE k x)) :=
  RowRefinement.homotopy qE qF hE hF (a := a) (b := b)
    (fun k x => by simpa only [Homotopy.at_zero] using hH k 0 x)
    (fun k x => by simpa only [Homotopy.at_one] using hH k 1 x) H hH

/-- Each time slice is the actual row map of the original time slice. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullHomotopy.lean:40"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem refineWholeRowHomotopy_at {E F : Topology.LoopPrespectrum.{u}}
    (qE : ∀ k, C(E.space (k + 3), E.space (k + 3)))
    (qF : ∀ k, C(F.space (k + 3), F.space (k + 3)))
    (hE : ∀ k, qE k (E.point (k + 3)) = E.point (k + 3))
    (hF : ∀ k, qF k (F.point (k + 3)) = F.point (k + 3))
    {a b : E ⟶ F} (H : Topology.LoopPrespectrum.Homotopy a b)
    (hH : ∀ k t x, qF k (H.level (k + 3) (t, x)) =
      H.level (k + 3) (t, qE k x)) (t : unitInterval) :
    (refineWholeRowHomotopy qE qF hE hF H hH).at t =
      RowRefinement.map qE qF hE hF (H.at t) (fun k x => hH k t x) := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  cases n <;> rfl

open ModelDiagramRowInterchange GeometricSeedCospan
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The original finite auxiliary null after the actual unlooped cone construction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullHomotopy.lean:60"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def fullConeNull (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  (diagramSquareMapHomotopy
    (η := (strictDiagramIterate squareFunctor i).map
        (Functor.whiskerRight (enlargement f T) prespectrumFunctor) ≫
      (strictDiagramIterate squareFunctor i).map
        (Functor.whiskerRight (restriction f T) prespectrumFunctor))
    (θ := diagramZeroMap
      ((strictDiagramIterate squareFunctor i).obj (fiber f T ⋙ prespectrumFunctor))
      ((strictDiagramIterate squareFunctor i).obj (openModel f T ⋙ prespectrumFunctor)))
    (strictDiagramIterateNull squareFunctor (fullNull f T) i).homotopy
    (strictDiagramIterateNull squareFunctor (fullNull f T) i).naturality
    (squareFunctor.obj X)).cone

/-- The same entire original cone null acts on the genuine proper row carriers. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullHomotopy.lean:74"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def fullRowNull (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  refineWholeRowHomotopy
    (cone squareFunctor i (fiber f T) X) (cone squareFunctor i (openModel f T) X)
    (cone_point squareFunctor i (fiber f T) X) (cone_point squareFunctor i (openModel f T) X)
    (fullConeNull f T i X) (fullNull_cone_row f T i X)

/-- Positive row levels retain the original null time and independent row coordinate. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullHomotopy.lean:81"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullRowNull_succ (i : ℕ) (X : Scheme.{u}ᵒᵖ) (k : ℕ) (t s : unitInterval)
    (γ : Path
      ((ModelDiagramRowRefinement.source squareFunctor i (fiber f T) X).point (k + 2))
      ((ModelDiagramRowRefinement.source squareFunctor i (fiber f T) X).point (k + 2))) :
    Path.toContinuousMap ((fullRowNull f T i X).level (k + 1) (t, γ)) s =
      (fullConeNull f T i X).level (k + 2) (t, γ s) := rfl

/-- Degree zero retains both original row-loop coordinates independently of null time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullHomotopy.lean:89"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullRowNull_zero (i : ℕ) (X : Scheme.{u}ᵒᵖ) (t s a : unitInterval)
    (γ : Path
      (Path.refl ((ModelDiagramRowRefinement.source squareFunctor i (fiber f T) X).point 2))
      (Path.refl ((ModelDiagramRowRefinement.source squareFunctor i (fiber f T) X).point 2))) :
    Path.toContinuousMap (Path.toContinuousMap ((fullRowNull f T i X).level 0 (t, γ)) s) a =
      (fullConeNull f T i X).level 2 (t, γ s a) := rfl

/-- The genuine row comparisons preserve the complete original null at exactly the same time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullHomotopy.lean:97"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullRowNull_comparison_at (i : ℕ) (X : Scheme.{u}ᵒᵖ) (t : unitInterval) :
    (fullConeNull f T i X).at t ≫
        ModelDiagramRowRefinement.comparison squareFunctor i (openModel f T) X =
      ModelDiagramRowRefinement.comparison squareFunctor i (fiber f T) X ≫
        (fullRowNull f T i X).at t := by
  rw [fullRowNull, refineWholeRowHomotopy_at]
  exact RowRefinement.comparison_naturality
    (cone squareFunctor i (fiber f T) X) (cone squareFunctor i (openModel f T) X)
    (cone_point squareFunctor i (fiber f T) X) (cone_point squareFunctor i (openModel f T) X)
    ((fullConeNull f T i X).at t) (fun k x => fullNull_cone_row f T i X k t x)
    (cone_structure squareFunctor i (fiber f T) X)
    (cone_structure squareFunctor i (openModel f T) X)

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
