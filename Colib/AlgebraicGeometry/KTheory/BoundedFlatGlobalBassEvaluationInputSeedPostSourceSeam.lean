/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedPostNullSeams
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedPostFace
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedInputFace

/-!
# The whole common word after the original input-first face

The full source unit edge and both postcomposed null paths agree in the actual mixed carrier. The
original inverse-null/unit/null word therefore has the same entire parameter on both routes,
including its independent seed time and its original half and quarter subdivisions.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity Topology SSet
open CategoryTheory.Waldhausen SmallWaldhausenCategory
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedPostSourceSeam
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedPostUnit
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

private def sourceFace : ⦋1⦌ ⟶ ⦋3⦌ := SimplexCategory.Hom.mk ⟨![0, 1], by decide⟩
private def targetFace : ⦋1⦌ ⟶ ⦋15⦌ := SimplexCategory.Hom.mk ⟨![3, 11], by decide⟩

/-- The complete strict source unit retains both its actual lower and shifted references. -/
private theorem unit_nodes (i : Fin 2) :
    InputMixedDesc.postNode g (InputSeedEvaluationNullUnit.unitNodes Y (sourceFace.toOrderHom i)) =
      InputSeedUnitNodes.nodes g (targetFace.toOrderHom i) := by
  have h0 : InputMixedDesc.postNode g (InputSeedEvaluationNullUnit.unitNodes Y 0) =
      InputSeedUnitNodes.lower g 3 :=
    (congrArg (InputMixedDesc.postNode g) (InputSeedEvaluationNullUnit.lower_nodes Y 0).symm).trans
      ((InputChartReference.post_nodes g plus GlobalRawBass.plus_projection 0).symm.trans
        (InputSeedUnitNodes.post_source g).symm)
  fin_cases i
  · exact h0
  · change InputMixedDesc.postNode g (InputSeedEvaluationNullUnit.unitNodes Y 1) =
      ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g)
        (InputSeedUnitNodes.lower g 3)
    exact (congrArg (InputMixedDesc.postNode g)
      (InputSeedEvaluationNullUnit.upper_nodes Y 0).symm).trans
      ((post_shift g (InputChartSimplex.nodes Y 0)).symm.trans
        (congrArg (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g))
          ((congrArg (InputMixedDesc.postNode g)
            (InputSeedEvaluationNullUnit.lower_nodes Y 0)).trans h0)))

/-- The entire original postcomposed unit agrees before applying any native evaluator. -/
theorem oldUnit (s : I) :
    InputSeedPostMap.map g (InputSeedEvaluationNullUnit.oldUnit Y s) =
      InputSeedInputFace.targetUnit g s := by
  change InputSeedPostMap.map g
    (CutOpenCarrier.laurentInclusion _ _ _ _ _
      (parameter (InputSeedEvaluationCarrier.laurentRef Y)
        (InputSeedEvaluationNullUnit.unitNodes Y) (edge (k := 3) 0 1 s))) = _
  rw [InputSeedPostMap.map_laurent, InputSeedInputFace.targetUnit_apply]
  change CutOpenCarrier.laurentInclusion _ _ _ _ _
    (mapParameter (InputMixedDesc.postNode g) (parameter _ _ (edge (k := 3) 0 1 s))) = _
  rw [mapParameter_parameter]
  congr 1
  have h := parameter_eq_of_face_nodes (InputSeedCarrier.laurentRef g)
    (InputSeedUnitNodes.nodes g)
    (fun i => InputMixedDesc.postNode g (InputSeedEvaluationNullUnit.unitNodes Y i))
    targetFace sourceFace (unit_nodes g) (edge (k := 1) 0 1 s)
  have hs : StdSimplex.map sourceFace.toOrderHom (edge (k := 1) 0 1 s) =
      edge (k := 3) 0 1 s := map_edge sourceFace 0 1 s
  have ht : StdSimplex.map targetFace.toOrderHom (edge (k := 1) 0 1 s) =
      edge (k := 15) 3 11 s := map_edge targetFace 0 1 s
  rw [hs, ht] at h
  exact h

/-- The common word keeps both complete null paths and the original middle unit. -/
theorem word (s : I) : InputSeedPostFace.sourceParameter g s =
    InputSeedInputFace.targetWord g s :=
  Path.Evaluation.path_trans (InputSeedPostMap.map g)
    (InputSeedEvaluationNull.oldNull Y false).symm
    ((InputSeedEvaluationNullUnit.oldUnit Y).trans (InputSeedEvaluationNull.oldNull Y true))
    (InputSeedInputNull.targetPath g false).symm
    ((InputSeedInputFace.targetUnit g).trans (InputSeedInputNull.targetPath g true))
    (Path.Evaluation.path_symm (InputSeedPostMap.map g)
      (InputSeedEvaluationNull.oldNull Y false) (InputSeedInputNull.targetPath g false)
      (InputSeedPostNullSeams.oldNull g false))
    (Path.Evaluation.path_trans (InputSeedPostMap.map g)
      (InputSeedEvaluationNullUnit.oldUnit Y) (InputSeedEvaluationNull.oldNull Y true)
      (InputSeedInputFace.targetUnit g) (InputSeedInputNull.targetPath g true)
      (oldUnit g) (InputSeedPostNullSeams.oldNull g true)) s

/-- The input-first face meets the postcomposed comparison on its entire original seed word. -/
theorem face (s : I) : InputSeedPostFace.parameter g (0, s) =
    InputSeedInputFace.parameter g (1, s) :=
  (InputSeedPostFace.source g s).trans
    ((word g s).trans (InputSeedInputFace.target g s).symm)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedPostSourceSeam
