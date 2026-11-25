/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityCarrierCharts
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0MergedBoundary

/-!
# Two whole carrier seams of the original global raw identity boundary

Both joins identify the actual codiscrete-nerve points, using equality of full dependent nodes
on the original five-node paths. Their original reversed and concatenated clocks are retained.
No equality of evaluated values is used to infer an equality in the carrier.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Convexity
open CategoryTheory.Waldhausen.IteratedS Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityCarrierSeams
open InputIdentityNodes InputIdentityCarrierCharts

/-- The five original unit-square boundary nodes occur in their actual increasing order. -/
def unitFace : ⦋4⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 1, 2, 4, 5], by decide⟩

/-- The entire positive boundary lies in the unchanged thirty-one-node input surface. -/
def plusFace : ⦋4⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![9, 10, 11, 12, 13], by decide⟩

/-- The inverse boundary retains its separate original node positions. -/
def minusFace : ⦋4⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![20, 21, 22, 23, 24], by decide⟩

variable (X : Scheme.{u})

/-- The two original unit rows identify the complete five-node chart boundary. -/
theorem chart_initial_nodes (k : laurent ⟶ polynomial)
    (hk : ∀ Z, k.app Z ≫ projection.app Z = laurentProjection.app Z) (i : Fin 5) :
    chartNodes X k hk (![9, 10, 11, 12, 13] i) =
      chartSideNodes X k hk (unitFace.toOrderHom i) := by
  fin_cases i
  · exact chart_unit_right X k hk 0
  · exact chart_unit_right X k hk 1
  · exact chart_unit_right X k hk 2
  · exact chart_unit_left X k hk 1
  · exact chart_unit_left X k hk 2

/-- Every positive seam vertex has the same original map and the same full reference anchor. -/
theorem plus_nodes (i : Fin 5) :
    nodes X (plusFace.toOrderHom i) =
      chartSideNodes X plus plus_projection (unitFace.toOrderHom i) := by
  fin_cases i
  · exact (InputIdentityNodes.plus_nodes X 9).trans
      (chart_initial_nodes X plus plus_projection 0)
  · exact (InputIdentityNodes.plus_nodes X 10).trans
      (chart_initial_nodes X plus plus_projection 1)
  · exact (InputIdentityNodes.plus_nodes X 11).trans
      (chart_initial_nodes X plus plus_projection 2)
  · exact (InputIdentityNodes.plus_nodes X 12).trans
      (chart_initial_nodes X plus plus_projection 3)
  · exact (InputIdentityNodes.plus_nodes X 13).trans
      (chart_initial_nodes X plus plus_projection 4)

/-- The inverse seam preserves its distinct original chart and every reference transformation. -/
theorem minus_nodes (i : Fin 5) :
    nodes X (minusFace.toOrderHom i) =
      chartSideNodes X minus minus_projection (unitFace.toOrderHom i) := by
  fin_cases i
  · exact (InputIdentityNodes.minus_nodes X 9).trans
      (chart_initial_nodes X minus minus_projection 0)
  · exact (InputIdentityNodes.minus_nodes X 10).trans
      (chart_initial_nodes X minus minus_projection 1)
  · exact (InputIdentityNodes.minus_nodes X 11).trans
      (chart_initial_nodes X minus minus_projection 2)
  · exact (InputIdentityNodes.minus_nodes X 12).trans
      (chart_initial_nodes X minus minus_projection 3)
  · exact (InputIdentityNodes.minus_nodes X 13).trans
      (chart_initial_nodes X minus minus_projection 4)

/-- The entire initial-positive join is an equality of actual continuous carrier paths. -/
theorem plus_seam :
    (inputFace X).comp ⟨fun s : unitInterval ↦ (s, 0), by fun_prop⟩ =
      (chartFace X plus plus_projection).comp
        ⟨fun s : unitInterval ↦ (0, s), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro s
  change CommonReferenceNerve.parameter (source X) (nodes X)
      (BoundedFlatCoefficientBassH0Diagram.parameter (s, 0)) =
    CommonReferenceNerve.parameter (source X) (chartSideNodes X plus plus_projection)
      (BoundedFlatPerfectOriginalUnitSquareSimplex.squareParameter (0, s))
  rw [BoundedFlatCoefficientBassH0Merged.h0_parameter_left,
    BoundedFlatPerfectOriginalUnitSquareSimplex.square_zero]
  let z := (((binaryPath (k := 4) 0 1 2).symm.trans (binaryPath 0 3 4)) s)
  have h₁ := CommonReferenceNerve.parameter_face (source X) (nodes X) plusFace z
  have h₂ := CommonReferenceNerve.parameter_face (source X)
    (chartSideNodes X plus plus_projection) unitFace z
  have h := h₁.trans ((congrArg (fun N ↦ CommonReferenceNerve.parameter (source X) N z)
    (funext (plus_nodes X))).trans h₂.symm)
  dsimp only [z] at h
  rw [BoundedFlatCoefficientBassH0Merged.map_two_binary,
    BoundedFlatCoefficientBassH0Merged.map_two_binary] at h
  exact h

/-- The inverse join retains the whole original carrier path at exactly the same clock. -/
theorem minus_seam :
    (inputFace X).comp ⟨fun s : unitInterval ↦ (s, 1), by fun_prop⟩ =
      (chartFace X minus minus_projection).comp
        ⟨fun s : unitInterval ↦ (0, s), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro s
  change CommonReferenceNerve.parameter (source X) (nodes X)
      (BoundedFlatCoefficientBassH0Diagram.parameter (s, 1)) =
    CommonReferenceNerve.parameter (source X) (chartSideNodes X minus minus_projection)
      (BoundedFlatPerfectOriginalUnitSquareSimplex.squareParameter (0, s))
  rw [BoundedFlatCoefficientBassH0Merged.h0_parameter_right,
    BoundedFlatPerfectOriginalUnitSquareSimplex.square_zero]
  let z := (((binaryPath (k := 4) 0 1 2).symm.trans (binaryPath 0 3 4)) s)
  have h₁ := CommonReferenceNerve.parameter_face (source X) (nodes X) minusFace z
  have h₂ := CommonReferenceNerve.parameter_face (source X)
    (chartSideNodes X minus minus_projection) unitFace z
  have h := h₁.trans ((congrArg (fun N ↦ CommonReferenceNerve.parameter (source X) N z)
    (funext (minus_nodes X))).trans h₂.symm)
  dsimp only [z] at h
  rw [BoundedFlatCoefficientBassH0Merged.map_two_binary,
    BoundedFlatCoefficientBassH0Merged.map_two_binary] at h
  exact h

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityCarrierSeams
