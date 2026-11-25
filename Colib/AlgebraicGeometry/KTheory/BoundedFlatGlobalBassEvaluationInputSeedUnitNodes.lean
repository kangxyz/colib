/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedRawUnit
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartNormNodes
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputLaurentSeams

/-!
# Sixteen complete Laurent-unit references for the mixed seed words

The actual Laurent commuting square supplies eight lower nodes. The common original strict
unit supplies eight separately anchored upper nodes. The five actual raw normalization nodes
and their shifted copies use the original raw source unit before evaluation and realization.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite
open Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedUnitNodes
open GlobalSectionChangeIndex CommonReferenceNerve

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Eight complete original references of the actual Laurent projection square. -/
def lower : Fin 8 → Node (InputSeedCarrier.laurentRef g) :=
  InputCommutingSimplex.nodes (laurent.map g) (GlobalRawBass.laurentProjection.app Y)
    (GlobalRawBass.laurentProjection.app X) g (GlobalRawBass.laurentProjection.naturality g)

/-- The eight upper references retain the actual common forward unit. -/
def upper (i : Fin 8) : Node (InputSeedCarrier.laurentRef g) :=
  ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g) (lower g i)

/-- Sixteen full nodes keep the lower and upper sheets separate. -/
def nodes : Fin 16 → Node (InputSeedCarrier.laurentRef g) :=
  ![lower g 0, lower g 1, lower g 2, lower g 3,
    lower g 4, lower g 5, lower g 6, lower g 7,
    upper g 0, upper g 1, upper g 2, upper g 3,
    upper g 4, upper g 5, upper g 6, upper g 7]

/-- The actual lower references form one ordered face. -/
def lowerFace : ⦋7⦌ ⟶ ⦋15⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 1, 2, 3, 4, 5, 6, 7], by decide⟩

/-- The separately anchored upper references form another ordered face. -/
def upperFace : ⦋7⦌ ⟶ ⦋15⦌ :=
  SimplexCategory.Hom.mk ⟨![8, 9, 10, 11, 12, 13, 14, 15], by decide⟩

/-- Every lower full node occurs unchanged. -/
theorem lower_nodes (i : Fin 8) : nodes g (lowerFace.toOrderHom i) = lower g i := by
  fin_cases i <;> rfl

/-- Every upper full node keeps the original unit anchor. -/
theorem upper_nodes (i : Fin 8) : nodes g (upperFace.toOrderHom i) = upper g i := by
  fin_cases i <;> rfl

/-- The first original reference has its actual identity anchor. -/
theorem lower_zero : lower g 0 = ⟨InputSeedCarrier.laurentRef g, Iso.refl _⟩ := rfl

/-- The first source agrees with the complete positive-chart source. -/
theorem pre_source : lower g 0 =
    InputChartReference.preNode g plus GlobalRawBass.plus_projection 0 :=
  (InputChartFaceNodes.source_node g plus GlobalRawBass.plus_projection).symm.trans
    (InputChartFaceNodes.pre_source_node g plus GlobalRawBass.plus_projection)

/-- The first Laurent evaluation cut is the complete original postcomposed chart source. -/
theorem post_source : lower g 3 =
    InputChartReference.postNode g plus GlobalRawBass.plus_projection 0 :=
  (InputLaurentSeams.cut_node g plus GlobalRawBass.plus_projection).symm.trans
    (InputChartFaceNodes.post_source_node g plus GlobalRawBass.plus_projection)

/-- Every upper anchor retains the original target action on the same underlying Model arrow. -/
theorem upper_anchor (i : Fin 8) :
    (upper g i).2 = (lower g i).2 ≪≫
      CategoryTheory.Functor.IdentityAutomorphism.onFunctor (lower g i).1.hom.toFunctor
        (evaluationSmallUnit (op (laurent.obj X))
          (laurentScalar (op X))) :=
  InputSeedCarrier.anchor_unit g (lower g i)

/-- The five actual binary normalization nodes are selected without changing either route. -/
def rawIndex : Fin 5 → Fin 8 := ![1, 2, 4, 5, 7]

/-- The complete raw lower family is the original five-node square after actual evaluation. -/
theorem raw_lower_nodes (i : Fin 5) :
    lower g (rawIndex i) = InputSeedRawUnit.evaluateNode g
      (BoundedFlatPerfectNativeSquareFiveSimplex.nodes (laurent.map g)
        (GlobalRawBass.laurentProjection.app Y)
        (GlobalRawBass.laurentProjection.app X) g
        (GlobalRawBass.laurentProjection.naturality g) i) :=
  (InputChartNormalizationNodes.commuting_normalization_nodes
    (laurent.map g) (GlobalRawBass.laurentProjection.app Y)
    (GlobalRawBass.laurentProjection.app X) g
    (GlobalRawBass.laurentProjection.naturality g) i).trans
      (InputSeedRawUnit.evaluateNode_eq g _).symm

/-- The full shifted raw family uses the same original unit before evaluation. -/
theorem raw_upper_nodes (i : Fin 5) :
    upper g (rawIndex i) = InputSeedRawUnit.evaluateNode g
      (ModelSimplex.reanchorNode (InputSeedRawUnit.rawUnit g)
        (BoundedFlatPerfectNativeSquareFiveSimplex.nodes (laurent.map g)
          (GlobalRawBass.laurentProjection.app Y)
          (GlobalRawBass.laurentProjection.app X) g
          (GlobalRawBass.laurentProjection.naturality g) i)) := by
  change ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g)
    (lower g (rawIndex i)) = _
  rw [raw_lower_nodes]
  exact InputSeedRawUnit.evaluate_shift g _

/-- The finite common-reference simplex retains all sixteen complete nodes. -/
def simplex : ModelSimplex (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (laurent.obj X).toRingedSpace)) 15 :=
  ModelSimplex.ofIsos (InputSeedCarrier.laurentRef g)
    (fun i => (nodes g i).1) (fun i => (nodes g i).2)

/-- The entire lower diagram is the original Laurent commuting-square diagram. -/
theorem lower_face : (simplex g).face lowerFace =
    InputCommutingSimplex.simplex (laurent.map g) (GlobalRawBass.laurentProjection.app Y)
      (GlobalRawBass.laurentProjection.app X) g
      (GlobalRawBass.laurentProjection.naturality g) := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (lower_nodes g)

/-- The upper family is the exact same diagram with its separate original unit reference. -/
theorem upper_face : (simplex g).face upperFace =
    InputCommutingSimplex.simplex (laurent.map g) (GlobalRawBass.laurentProjection.app Y)
      (GlobalRawBass.laurentProjection.app X) g
      (GlobalRawBass.laurentProjection.naturality g) := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _ _ (upper_nodes g)).trans
    (ModelSimplex.ofIsos_change_reference (InputSeedCarrier.commonUnit g)
      (fun i => (lower g i).1) (fun i => (lower g i).2))

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedUnitNodes
