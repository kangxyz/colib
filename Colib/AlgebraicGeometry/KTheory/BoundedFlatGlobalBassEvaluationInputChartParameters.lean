/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartPostAttachment
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartPreAttachment
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartSelection

/-!
# Whole characteristic parameters of both mixed chart attachments

Equality of all original dependent nodes identifies every point of both chart attachments
with their selected faces in the actual mixed descent nerve.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartReference
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- The whole Y characteristic map is the original chart followed by actual attachment. -/
theorem post_parameter (z : StdSimplex ℝ (Fin 5)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (postNode g k hk) z =
      CommonReferenceNerve.mapParameter (InputMixedDesc.postNode g)
        (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap Y)
          (InputChartSimplex.chartNodes Y (k.app Y) (hk Y)) z) := by
  rw [CommonReferenceNerve.mapParameter_parameter]
  exact congrArg (fun N => CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) N z)
    (funext (post_nodes g k hk))

/-- The whole X characteristic map keeps the actual strict reference attachment. -/
theorem pre_parameter (z : StdSimplex ℝ (Fin 5)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (preNode g k hk) z =
      CommonReferenceNerve.mapParameter (InputMixedDesc.preNode g)
        (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X)
          (InputChartSimplex.chartNodes X (k.app X) (hk X)) z) := by
  rw [CommonReferenceNerve.mapParameter_parameter]
  exact congrArg (fun N => CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) N z)
    (funext (pre_nodes g k hk))

/-- Every point of the positive Y chart is its prescribed mixed descent face. -/
theorem plus_post_parameter (z : StdSimplex ℝ (Fin 5)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (postNode g plus GlobalRawBass.plus_projection) z =
    CommonReferenceNerve.mapParameter (InputMixedDesc.postNode g)
      (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap Y) (InputChartSimplex.nodes Y)
        (StdSimplex.map InputChartSimplex.plusFace.toOrderHom z)) :=
  (post_parameter g plus GlobalRawBass.plus_projection z).trans
    (congrArg (CommonReferenceNerve.mapParameter (InputMixedDesc.postNode g))
      (plus_parameter Y z).symm)

/-- Every inverse Y chart point retains its complete shared source and total anchors. -/
theorem minus_post_parameter (z : StdSimplex ℝ (Fin 5)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (postNode g minus GlobalRawBass.minus_projection) z =
    CommonReferenceNerve.mapParameter (InputMixedDesc.postNode g)
      (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap Y) (InputChartSimplex.nodes Y)
        (StdSimplex.map InputChartSimplex.minusFace.toOrderHom z)) :=
  (post_parameter g minus GlobalRawBass.minus_projection z).trans
    (congrArg (CommonReferenceNerve.mapParameter (InputMixedDesc.postNode g))
      (minus_parameter Y z).symm)

/-- Every positive X chart point is the original strict-precomposed descent face. -/
theorem plus_pre_parameter (z : StdSimplex ℝ (Fin 5)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (preNode g plus GlobalRawBass.plus_projection) z =
    CommonReferenceNerve.mapParameter (InputMixedDesc.preNode g)
      (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X) (InputChartSimplex.nodes X)
        (StdSimplex.map InputChartSimplex.plusFace.toOrderHom z)) :=
  (pre_parameter g plus GlobalRawBass.plus_projection z).trans
    (congrArg (CommonReferenceNerve.mapParameter (InputMixedDesc.preNode g))
      (plus_parameter X z).symm)

/-- Every inverse X chart point keeps its full reference before the evaluation bridges. -/
theorem minus_pre_parameter (z : StdSimplex ℝ (Fin 5)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (preNode g minus GlobalRawBass.minus_projection) z =
    CommonReferenceNerve.mapParameter (InputMixedDesc.preNode g)
      (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X) (InputChartSimplex.nodes X)
        (StdSimplex.map InputChartSimplex.minusFace.toOrderHom z)) :=
  (pre_parameter g minus GlobalRawBass.minus_projection z).trans
    (congrArg (CommonReferenceNerve.mapParameter (InputMixedDesc.preNode g))
      (minus_parameter X z).symm)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartReference
