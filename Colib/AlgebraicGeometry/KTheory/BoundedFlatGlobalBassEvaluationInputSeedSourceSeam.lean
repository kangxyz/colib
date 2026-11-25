/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedStrictNullSeams
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedStrictFace
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedInputFace

/-!
# The complete common initial word of the two original mixed seed routes

The full source unit edge and both source null paths agree in the actual mixed carrier. The
original inverse-null/unit/null word therefore has the same entire parameter on both routes,
including its independent seed time and its original half and quarter subdivisions.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity Topology
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedSourceSeam
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedStrictAttachment
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

private def sourceFace : ⦋1⦌ ⟶ ⦋3⦌ := SimplexCategory.Hom.mk ⟨![0, 1], by decide⟩
private def targetFace : ⦋1⦌ ⟶ ⦋15⦌ := SimplexCategory.Hom.mk ⟨![0, 8], by decide⟩

/-- The complete strict source unit retains both its actual lower and shifted references. -/
private theorem unit_nodes (i : Fin 2) :
    laurentNode g (InputSeedEvaluationNullUnit.unitNodes X (sourceFace.toOrderHom i)) =
      InputSeedUnitNodes.nodes g (targetFace.toOrderHom i) := by
  have h0 : laurentNode g (InputSeedEvaluationNullUnit.unitNodes X 0) =
      InputSeedUnitNodes.lower g 0 :=
    (congrArg (laurentNode g) (InputSeedEvaluationNullUnit.lower_nodes X 0).symm).trans
      ((InputChartReference.pre_nodes g plus GlobalRawBass.plus_projection 0).symm.trans
        (InputSeedUnitNodes.pre_source g).symm)
  fin_cases i
  · exact h0
  · change laurentNode g (InputSeedEvaluationNullUnit.unitNodes X 1) =
      ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g)
        (InputSeedUnitNodes.lower g 0)
    exact (congrArg (laurentNode g) (InputSeedEvaluationNullUnit.upper_nodes X 0).symm).trans
      ((laurent_shift g (InputChartSimplex.nodes X 0)).symm.trans
        (congrArg (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g))
          ((congrArg (laurentNode g) (InputSeedEvaluationNullUnit.lower_nodes X 0)).trans h0)))

/-- The entire original strict unit agrees before applying any native evaluator. -/
theorem oldUnit (s : I) :
    InputSeedStrictMap.map g (InputSeedEvaluationNullUnit.oldUnit X s) =
      InputSeedInputFace.sourceUnit g s := by
  change InputSeedStrictMap.map g
    (CutOpenCarrier.laurentInclusion _ _ _ _ _
      (parameter (InputSeedEvaluationCarrier.laurentRef X)
        (InputSeedEvaluationNullUnit.unitNodes X) (edge (k := 3) 0 1 s))) = _
  rw [InputSeedStrictMap.map_laurent, InputSeedInputFace.sourceUnit_apply]
  change CutOpenCarrier.laurentInclusion _ _ _ _ _
    (mapParameter (laurentNode g) (parameter _ _ (edge (k := 3) 0 1 s))) = _
  rw [mapParameter_parameter]
  congr 1
  have h := parameter_eq_of_face_nodes (InputSeedCarrier.laurentRef g)
    (InputSeedUnitNodes.nodes g)
    (fun i ↦ laurentNode g (InputSeedEvaluationNullUnit.unitNodes X i))
    targetFace sourceFace (unit_nodes g) (edge (k := 1) 0 1 s)
  have hs : StdSimplex.map sourceFace.toOrderHom (edge (k := 1) 0 1 s) =
      edge (k := 3) 0 1 s := map_edge sourceFace 0 1 s
  have ht : StdSimplex.map targetFace.toOrderHom (edge (k := 1) 0 1 s) =
      edge (k := 15) 0 8 s := map_edge targetFace 0 1 s
  rw [hs, ht] at h
  exact h

/-- The entire common initial word keeps both null halves and the original middle unit. -/
theorem word (s : I) : InputSeedStrictFace.sourceParameter g s =
    InputSeedInputFace.sourceWord g s :=
  Path.Evaluation.path_trans (InputSeedStrictMap.map g)
    (InputSeedEvaluationNull.oldNull X false).symm
    ((InputSeedEvaluationNullUnit.oldUnit X).trans (InputSeedEvaluationNull.oldNull X true))
    (InputSeedInputNull.sourcePath g false).symm
    ((InputSeedInputFace.sourceUnit g).trans (InputSeedInputNull.sourcePath g true))
    (Path.Evaluation.path_symm (InputSeedStrictMap.map g)
      (InputSeedEvaluationNull.oldNull X false) (InputSeedInputNull.sourcePath g false)
      (InputSeedStrictNullSeams.oldNull g false))
    (Path.Evaluation.path_trans (InputSeedStrictMap.map g)
      (InputSeedEvaluationNullUnit.oldUnit X) (InputSeedEvaluationNull.oldNull X true)
      (InputSeedInputFace.sourceUnit g) (InputSeedInputNull.sourcePath g true)
      (oldUnit g) (InputSeedStrictNullSeams.oldNull g true)) s

/-- The two prescribed first faces share their complete original initial seed path. -/
theorem face (s : I) : InputSeedStrictFace.parameter g (0, s) =
    InputSeedInputFace.parameter g (0, s) :=
  (InputSeedStrictFace.source g s).trans
    ((word g s).trans (InputSeedInputFace.source g s).symm)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedSourceSeam
