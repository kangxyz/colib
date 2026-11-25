/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartNormNodes
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanParameterNodes
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputRawChartProductNodes
public import Colib.KTheory.Waldhausen.Iterated.ReferenceWhiskeringFamily

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartPrism
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSquarePathSupport

/-!
# The original polynomial row in the attached span comparison

One complete terminal node pins the entire five-node raw polynomial square. Both representations
retain the same actual evaluation and raw chart suffix, with their original reference anchors.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanTargetNodes
open GlobalSectionChangeIndex ModelSimplex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

private abbrev rawSource :=
  BoundedFlatPerfectNativeSquareFiveSimplex.source (polynomial.map g) (projection.app Y)
private abbrev rawNodes :=
  BoundedFlatPerfectNativeSquareFiveSimplex.nodes (polynomial.map g) (projection.app Y)
  (projection.app X) g (projection.naturality g)

private def attachedAnchor : (InputMixedDesc.sourceMap g).hom.toFunctor ≅
    (evaluationModel (op Y) ≫ rawSource g ≫ evaluationRawMap (k.app X)).hom.toFunctor :=
  InputSpanParameterNodes.sourceIso g k hk ≪≫
    isoWhiskerRight (evaluationComparisonIso (polynomial.map g ≫ projection.app Y))
      (evaluationRawMap (k.app X)).hom.toFunctor

private def rectangleAnchor : (InputMixedDesc.sourceMap g).hom.toFunctor ≅
    (evaluationModel (op Y) ≫ rawSource g ≫ evaluationRawMap (k.app X)).hom.toFunctor :=
  evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y) ≪≫
    isoWhiskerLeft (evaluationModel (op Y)).hom.toFunctor
      (BoundedFlatPerfectProjectionChartSquareRow.polynomialAnchor (projection.app Y) (k.app Y)
        (k.app X) (polynomial.map g) (laurent.map g) (k.naturality g)
        (GlobalRawBass.laurentProjection.app Y) (hk Y))

private theorem attached_nodes (i : Fin 5) :
    InputSpanParameterNodes.nodes g k hk (InputChartNormalizationNodes.normalizationRow i) =
      prePostNodes (InputMixedDesc.sourceMap g) (evaluationModel (op Y))
        (evaluationRawMap (k.app X)) (rawSource g) (rawNodes g)
        (attachedAnchor g k hk) i := by
  change postReferenceNode (InputMixedDesc.sourceMap g) (evaluationRawMap (k.app X))
    (InputSpanParameterNodes.sourceIso g k hk)
    (InputCommutingSimplex.nodes (polynomial.map g) (projection.app Y)
      (projection.app X) g (projection.naturality g)
        (InputChartNormalizationNodes.normalizationRow i)) = _
  rw [InputChartNormalizationNodes.commuting_normalization_nodes]
  exact post_pre_node (InputMixedDesc.sourceMap g) (evaluationModel (op Y))
    (evaluationRawMap (k.app X)) (rawSource g) (rawNodes g)
    (evaluationComparisonIso (polynomial.map g ≫ projection.app Y))
    (InputSpanParameterNodes.sourceIso g k hk) i

private theorem rectangle_nodes (i : Fin 5) :
    InputChartReference.rawNode g k hk
      (BoundedFlatPerfectProjectionChartSquareRow.polynomialRow i) =
      prePostNodes (InputMixedDesc.sourceMap g) (evaluationModel (op Y))
        (evaluationRawMap (k.app X)) (rawSource g) (rawNodes g)
        (rectangleAnchor g k hk) i := by
  rw [InputRawDesc.chart_node]
  unfold GlobalRawBass.InputDescSimplex.chartNodes
  rw [BoundedFlatPerfectProjectionChartSquareRow.polynomial_row_nodes]
  exact pre_post_node (InputMixedDesc.sourceMap g) (evaluationModel (op Y))
    (evaluationRawMap (k.app X)) (rawSource g) (rawNodes g)
    (BoundedFlatPerfectProjectionChartSquareRow.polynomialAnchor (projection.app Y) (k.app Y)
      (k.app X) (polynomial.map g) (laurent.map g) (k.naturality g)
      (GlobalRawBass.laurentProjection.app Y) (hk Y))
    (evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y)) i

/-- The complete terminal projection node is the original terminal raw rectangle node. -/
theorem terminal_node :
    InputSpanParameterNodes.nodes g k hk 7 = InputChartReference.rawNode g k hk 17 :=
  (InputSpanParameterNodes.node_seven g k hk).trans
    (InputChartReference.prism_raw_nodes g k hk 2)

/-- All five raw polynomial nodes agree with their full original rectangle references. -/
theorem raw_nodes (i : Fin 5) :
    InputSpanParameterNodes.nodes g k hk (InputChartNormalizationNodes.normalizationRow i) =
      InputChartReference.rawNode g k hk
        (BoundedFlatPerfectProjectionChartSquareRow.polynomialRow i) :=
  prePost_families_match (InputMixedDesc.sourceMap g) (evaluationModel (op Y))
    (evaluationRawMap (k.app X)) (rawSource g) (rawNodes g)
    (attached_nodes g k hk) (rectangle_nodes g k hk) 4 (terminal_node g k hk) i

/-- The target of the attached evaluation column is the actual raw product terminal node. -/
theorem column_terminal_node :
    InputSpanParameterNodes.nodes g k hk 4 = InputRawChartProductNodes.nodes g k hk 9 := by
  exact (raw_nodes g k hk 2).trans
    ((InputRawDesc.chart_node g k hk 13).trans
      ((InputRawChartRows.chart_nodes g k hk 4).trans
        (InputRawChartProductNodes.terminal_nodes g k hk 4).symm))

/-- The entire original reverse-forward polynomial path retains its four primitive edges. -/
theorem raw_parameter (t : unitInterval) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputSpanParameterNodes.nodes g k hk)
      (StdSimplex.map InputChartNormalizationNodes.normalizationRow
        (BoundedFlatPerfectNativeSquareFiveSimplex.parameter t)) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputChartReference.rawNode g k hk)
      (StdSimplex.map BoundedFlatPerfectProjectionChartSquareRow.polynomialRow
        (BoundedFlatPerfectNativeSquareFiveSimplex.parameter t)) := by
  obtain ⟨i, z, hz⟩ := BoundedFlatPerfectNativeSquareFiveSimplex.square_path_in t
  rw [← hz]
  exact (CommonReferenceNerve.parameter_supported (InputMixedDesc.sourceMap g)
    (fun j => InputSpanParameterNodes.nodes g k hk
      (InputChartNormalizationNodes.normalizationRow j))
    (InputSpanParameterNodes.nodes g k hk) InputChartNormalizationNodes.normalizationRow
      (fun _ => rfl)
    (BoundedFlatPerfectNativeSquareFiveSimplex.edgeFace i)
    ((by decide : ∀ j : Fin 4,
      Monotone (InputChartNormalizationNodes.normalizationRow ∘
        (BoundedFlatPerfectNativeSquareFiveSimplex.edgeFace j).toOrderHom)) i)
    z).trans
      (CommonReferenceNerve.parameter_supported (InputMixedDesc.sourceMap g)
        (fun j => InputSpanParameterNodes.nodes g k hk
          (InputChartNormalizationNodes.normalizationRow j))
        (InputChartReference.rawNode g k hk)
          BoundedFlatPerfectProjectionChartSquareRow.polynomialRow
        (fun j => (raw_nodes g k hk j).symm) (BoundedFlatPerfectNativeSquareFiveSimplex.edgeFace i)
        ((by decide : ∀ j : Fin 4, Monotone
          (BoundedFlatPerfectProjectionChartSquareRow.polynomialRow ∘
          (BoundedFlatPerfectNativeSquareFiveSimplex.edgeFace j).toOrderHom)) i) z).symm

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanTargetNodes
