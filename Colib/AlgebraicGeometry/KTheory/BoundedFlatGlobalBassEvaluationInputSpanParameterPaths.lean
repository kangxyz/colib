/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanParameterWord
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanTargetNodes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputRawDesc
public import Colib.Topology.Path.EvaluationFactorExtraction
public import Colib.Topology.Realization.SimplexProductGrid

/-!
# The original five-piece target paths of the input-span parameter

The original evaluation column and polynomial square are recovered from their entire top
chart. The five resulting leaves agree with the original raw pasted target word, including
both normalization halves and all nested concatenation coordinates.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterTarget
open GlobalSectionChangeIndex InputSpanParameterWord BoundedFlatPerfectProjectionRectangleParameters
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

private theorem first_values {Z : Type*} [TopologicalSpace Z] (f : C(unitInterval, Z))
    {a b c : Z} (p : Path a b) (q : Path b c)
    (h : ∀ t, f t = (p.trans q) t) (t : unitInterval) :
    f (Path.CarrierHalfPaths.lower t) = p t :=
  Path.Evaluation.left_factor id (Path.CarrierHalfPaths.first f) (Path.CarrierHalfPaths.last f)
    p q (fun s ↦ (Path.CarrierHalfPaths.trans_apply f s).trans (h s)) t

private theorem last_values {Z : Type*} [TopologicalSpace Z] (f : C(unitInterval, Z))
    {a b c : Z} (p : Path a b) (q : Path b c)
    (h : ∀ t, f t = (p.trans q) t) (t : unitInterval) :
    f (Path.CarrierHalfPaths.upper t) = q t :=
  Path.Evaluation.right_factor id (Path.CarrierHalfPaths.first f) (Path.CarrierHalfPaths.last f)
    p q (fun s ↦ (Path.CarrierHalfPaths.trans_apply f s).trans (h s)) t

private def rawPath :=
  ((binaryPath (k := 7) 1 2 4).symm).trans (binaryPath 1 5 7)

private def chartTop : C(unitInterval, Carrier g) :=
  ⟨fun s ↦ chartSwap g k hk (s, 1), by fun_prop⟩

private theorem chart_top (s : unitInterval) :
    chartTop g k hk s =
      (((edge (k := 7) 3 4).map
        (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
          (InputSpanParameterNodes.nodes g k hk)).continuous).trans
        (rawPath.map (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
          (InputSpanParameterNodes.nodes g k hk)).continuous)) s := by
  change CommonReferenceNerve.parameter _ _ (InputCommutingParameter.parameter (1, s)) = _
  rw [InputCommutingParameter.parameter_one]
  rw [Path.trans_apply, Path.trans_apply]
  split <;> rfl

/-- The exact first half of either original chart is its complete evaluation edge. -/
theorem chart_initial (s : unitInterval) :
    chartSwap g k hk (Path.CarrierHalfPaths.lower s, 1) =
      CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
        (InputSpanParameterNodes.nodes g k hk) ((edge (k := 7) 3 4) s) :=
  first_values (chartTop g k hk)
    ((edge (k := 7) 3 4).map
      (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
        (InputSpanParameterNodes.nodes g k hk)).continuous)
    (rawPath.map (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputSpanParameterNodes.nodes g k hk)).continuous)
    (chart_top g k hk) s

private theorem map_edge_function {l m : ℕ} (f : Fin (l + 1) → Fin (m + 1))
    (i j : Fin (l + 1)) (s : unitInterval) :
    StdSimplex.map f (edge i j s) = edge (f i) (f j) s :=
  StdSimplex.map_duple (unitInterval.nonneg (unitInterval.symm s))
    (unitInterval.nonneg s) (by simp) i j f

private theorem map_binary_function {l m : ℕ} (f : Fin (l + 1) → Fin (m + 1))
    (i j v : Fin (l + 1)) (s : unitInterval) :
    StdSimplex.map f (binaryPath i j v s) = binaryPath (f i) (f j) (f v) s :=
  map_trans_values _ _ _ _ _ (map_edge_function f i j) (map_edge_function f j v) s

private theorem map_square_function {m : ℕ} (f : Fin 5 → Fin (m + 1))
    (s : unitInterval) :
    StdSimplex.map f (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) =
      ((binaryPath (f 0) (f 1) (f 2)).symm.trans
        (binaryPath (f 0) (f 3) (f 4))) s :=
  map_trans_values _ _ _ _ _ (fun t ↦ map_binary_function f 0 1 2 (unitInterval.symm t))
    (map_binary_function f 0 3 4) s

/-- The whole second half is the original polynomial reverse-forward square path. -/
theorem chart_last (s : unitInterval) :
    chartSwap g k hk (Path.CarrierHalfPaths.upper s, 1) =
      CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
        (InputChartReference.rawNode g k hk) ((Ppath (𝟙 ⦋17⦌)) s) := by
  have h := last_values (chartTop g k hk)
    ((edge (k := 7) 3 4).map
      (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
        (InputSpanParameterNodes.nodes g k hk)).continuous)
    (rawPath.map (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputSpanParameterNodes.nodes g k hk)).continuous)
    (chart_top g k hk) s
  refine h.trans ?_
  have hr := InputSpanTargetNodes.raw_parameter g k hk s
  rw [map_square_function, map_square_function] at hr
  exact hr

/-- The entire converted prism row retains its two original raw normalization edges. -/
theorem normalization_top (s : unitInterval) :
    normalizationSwap g k hk (s, 1) =
      CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
        (InputChartReference.rawNode g k hk) (binaryPath 15 16 17 s) := by
  change InputSpanParameterPrism.parameter g k hk (1, s) = _
  rw [InputSpanParameterPrism.parameter_eq]
  rw [show (edge (k := 1) 0 1) 1 = StdSimplex.single 1 from (edge 0 1).target]
  have hp := InputChartReference.prism_raw_parameter g k hk
    (InputSpanParameterPrism.splitPath s)
  rw [Topology.SimplexGrid.parameter_row] at hp ⊢
  refine hp.trans (congrArg
    (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputChartReference.rawNode g k hk)) ?_)
  exact map_trans_values _ _ _ _ _
    (map_triangle_edge InputRectangleNodes.preNormalizationFace 0 1)
    (map_triangle_edge InputRectangleNodes.preNormalizationFace 1 2) s

/-- The characteristic map of the complete original two-chart raw diagram. -/
def targetCharacteristic :=
  CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
    (InputRawDesc.nodes g)

private theorem plus_last (s : unitInterval) :
    lastPlus g s = targetCharacteristic g (Ppath BoundedFlatCoefficientBassH0Diagram.plusFace
      s) := by
  have h := chart_last g plus GlobalRawBass.plus_projection s
  refine h.trans ?_
  have hm := (InputRawDesc.plus_chart_characteristic g (Ppath (𝟙 ⦋17⦌) s)).symm
  refine hm.trans (congrArg (targetCharacteristic g) ?_)
  exact map_trans_values _ _ _ _ _
    (fun t ↦ map_binaryPath BoundedFlatCoefficientBassH0Diagram.plusFace 5 6 13
      (unitInterval.symm t))
    (map_binaryPath BoundedFlatCoefficientBassH0Diagram.plusFace 5 7 17) s

private theorem minus_last (s : unitInterval) :
    lastMinus g s = targetCharacteristic g (Ppath BoundedFlatCoefficientBassH0Diagram.minusFace
      s) := by
  have h := chart_last g minus GlobalRawBass.minus_projection s
  refine h.trans ?_
  have hm := (InputRawDesc.minus_chart_characteristic g (Ppath (𝟙 ⦋17⦌) s)).symm
  refine hm.trans (congrArg (targetCharacteristic g) ?_)
  exact map_trans_values _ _ _ _ _
    (fun t ↦ map_binaryPath BoundedFlatCoefficientBassH0Diagram.minusFace 5 6 13
      (unitInterval.symm t))
    (map_binaryPath BoundedFlatCoefficientBassH0Diagram.minusFace 5 7 17) s

private theorem plus_normalization (s : unitInterval) :
    normalizationSwap g plus GlobalRawBass.plus_projection (s, 1) =
      targetCharacteristic g (K BoundedFlatCoefficientBassH0Diagram.plusFace s) :=
  (normalization_top g plus GlobalRawBass.plus_projection s).trans
    ((InputRawDesc.plus_chart_characteristic g (binaryPath 15 16 17 s)).symm.trans
      (congrArg (targetCharacteristic g)
        (map_binaryPath BoundedFlatCoefficientBassH0Diagram.plusFace 15 16 17 s)))

private theorem minus_normalization (s : unitInterval) :
    normalizationSwap g minus GlobalRawBass.minus_projection (s, 1) =
      targetCharacteristic g (K BoundedFlatCoefficientBassH0Diagram.minusFace s) :=
  (normalization_top g minus GlobalRawBass.minus_projection s).trans
    ((InputRawDesc.minus_chart_characteristic g (binaryPath 15 16 17 s)).symm.trans
      (congrArg (targetCharacteristic g)
        (map_binaryPath BoundedFlatCoefficientBassH0Diagram.minusFace 15 16 17 s)))

private theorem overlap_top (s : unitInterval) :
    overlapTop g s = targetCharacteristic g
      (((K BoundedFlatCoefficientBassH0Diagram.plusFace).symm.trans
        (K BoundedFlatCoefficientBassH0Diagram.minusFace)) s) := by
  change overlapSwap g (s, 1) = _
  unfold overlapSwap
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split
  · exact plus_normalization g (unitInterval.symm _)
  · exact minus_normalization g _

/-- The entire central raw target word retains both original square paths and overlap. -/
theorem middle_top (s : unitInterval) :
    ((lastPlus g).trans ((overlapTop g).trans (lastMinus g).symm)) s =
      InputRawDesc.parameter g (1, s) := by
  rw [InputRawDesc.parameter_one_word]
  change _ = targetCharacteristic g _
  rw [Path.trans_apply, Path.trans_apply]
  split
  · exact plus_last g _
  · rw [Path.trans_apply, Path.trans_apply]
    split
    · exact overlap_top g _
    · exact minus_last g (unitInterval.symm _)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterTarget
