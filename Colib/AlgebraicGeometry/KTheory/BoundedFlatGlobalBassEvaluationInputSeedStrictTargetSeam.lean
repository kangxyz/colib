/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedStrictNullSeams
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedStrictFace
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvalBinaryEnds
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvalFace

/-!
# The whole original join between strict-input seed and moving evaluation

The unconverted prism row is the original strict-precomposed binary path. Its complete terminal
polynomial node and both raw-unit references identify the entire common word, preserving both
null sheets and the original nested seed clock.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite Topology Convexity
open CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedStrictTargetSeam
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedStrictAttachment

private theorem parameter_single_eq
    {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} (F : V ⟶ W) {p q : ℕ}
    (N : Fin (p + 1) → Node F) (M : Fin (q + 1) → Node F)
    (i : Fin (p + 1)) (j : Fin (q + 1)) (h : N i = M j) :
    parameter F N (StdSimplex.single i) = parameter F M (StdSimplex.single j) := by
  let α : ⦋0⦌ ⟶ ⦋p⦌ := SimplexCategory.Hom.mk ⟨fun _ ↦ i, fun _ _ _ ↦ le_rfl⟩
  let β : ⦋0⦌ ⟶ ⦋q⦌ := SimplexCategory.Hom.mk ⟨fun _ ↦ j, fun _ _ _ ↦ le_rfl⟩
  have e := parameter_eq_of_face_nodes F M N β α (fun _ ↦ h) (StdSimplex.single 0)
  rw [StdSimplex.map_single, StdSimplex.map_single] at e
  exact e

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The entire original binary row agrees before either actual sheet inclusion. -/
theorem binary_parameter (s : I) : InputSeedEvalBinary.parameter g (0, s) =
    mapParameter (laurentNode g)
      (parameter (InputSeedEvaluationCarrier.laurentRef X) (InputChartSimplex.nodes X)
        (binaryPath (k := 7) 1 2 4 s)) := by
  rw [InputSeedEvalBinary.source_parameter]
  have h₀ : StdSimplex.map
      (InputSimplex.triangleFace 1 2 4 (by decide) (by decide)).toOrderHom
      (binaryPath (k := 2) 0 1 2 s) = binaryPath (k := 4) 1 2 4 s :=
    map_binaryPath (InputSimplex.triangleFace 1 2 4 (by decide) (by decide)) 0 1 2 s
  rw [h₀]
  have h := InputChartReference.plus_pre_parameter g (binaryPath (k := 4) 1 2 4 s)
  have h₁ : StdSimplex.map InputChartSimplex.plusFace.toOrderHom
      (binaryPath (k := 4) 1 2 4 s) = binaryPath (k := 7) 1 2 4 s :=
    map_binaryPath InputChartSimplex.plusFace 1 2 4 s
  rw [h₁] at h
  exact h

/-- Both original binary halves survive on each separately anchored sheet. -/
theorem newPositive (e : Bool) (s : I) :
    InputSeedStrictMap.map g (InputSeedEvaluationNullChart.newPositive X e s) =
      InputSeedEvalNull.binarySwap g e (s, 0) := by
  have hs := InputSeedStrictNullSeams.sheet_parameter g e (InputChartSimplex.nodes X)
    (binaryPath (k := 7) 1 2 4 s)
  have h : InputSeedStrictMap.map g (InputSeedEvaluationNullChart.newPositive X e s) =
      InputSeedInputNull.sheet g e
        (mapParameter (laurentNode g)
          (parameter (InputSeedEvaluationCarrier.laurentRef X) (InputChartSimplex.nodes X)
            (binaryPath (k := 7) 1 2 4 s))) := by
    cases e <;> exact hs
  exact h.trans (congrArg (InputSeedInputNull.sheet g e) (binary_parameter g s).symm)

/-- The actual terminal polynomial node is the first node of the unchanged evaluation edge. -/
theorem polynomial_one :
    InputSeedStrictMap.polynomialMap g (InputSeedEvaluationCarrier.movement X 1) =
      InputSeedEvalBinary.polynomialParameter g 0 := by
  change mapParameter (polynomialNode g)
    (parameter (InputSeedEvaluationCarrier.polyRef X)
      (InputSeedEvaluationCarrier.polynomialNodes X) (edge (k := 1) 0 1 1)) =
    parameter (InputSeedCarrier.polyRef g) (InputSpanParameterNodes.projectionNodes g)
      (edge (k := 7) 6 7 0)
  rw [mapParameter_parameter, (edge (k := 1) 0 1).target, (edge (k := 7) 6 7).source]
  exact parameter_single_eq (InputSeedCarrier.polyRef g)
    (fun i => polynomialNode g (InputSeedEvaluationCarrier.polynomialNodes X i))
    (InputSpanParameterNodes.projectionNodes g) 1 6 (InputSeedStrictAttachment.polynomial_one g)

/-- The whole original final cylinder keeps its exact height at the shared polynomial node. -/
theorem newCone (e : Bool) (s : I) :
    InputSeedStrictMap.map g (InputSeedEvaluationNullChart.newCone X e s) =
      InputSeedEvalNull.cylinderSwap g e (s, 0) := by
  cases e
  · change InputSeedStrictMap.map g (CutOpenCarrier.cylinderMinus _ _ _ _ _
      (InputSeedEvaluationCarrier.movement X 1, s)) = _
    rw [InputSeedStrictMap.map_cylinderMinus, polynomial_one]
    rfl
  · change InputSeedStrictMap.map g (CutOpenCarrier.cylinderPlus _ _ _ _ _
      (InputSeedEvaluationCarrier.movement X 1, s)) = _
    rw [InputSeedStrictMap.map_cylinderPlus, polynomial_one]
    rfl

/-- The entire binary/cylinder null agrees with the original moving-input source word. -/
theorem newNull (e : Bool) (s : I) :
    InputSeedStrictMap.map g (InputSeedEvaluationNull.newNull X e s) =
      InputSeedEvalNull.path g e 0 s := by
  change InputSeedStrictMap.map g
    (((InputSeedEvaluationNullChart.newPositive X e).trans
      (InputSeedEvaluationNullChart.newCone X e)) s) =
    ((InputSeedEvalNull.binarySwap g e).trans (InputSeedEvalNull.cylinderSwap g e)) (s, 0)
  rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split
  · exact newPositive g e _
  · exact newCone g e _

private def sourceFace : ⦋1⦌ ⟶ ⦋3⦌ := SimplexCategory.Hom.mk ⟨![2, 3], by decide⟩
private def targetFace : ⦋1⦌ ⟶ ⦋15⦌ := SimplexCategory.Hom.mk ⟨![6, 14], by decide⟩

/-- Both full terminal unit nodes are the original unconverted evaluation-product corners. -/
private theorem unit_nodes (i : Fin 2) :
    laurentNode g (InputSeedEvaluationNullUnit.unitNodes X (sourceFace.toOrderHom i)) =
      InputSeedUnitNodes.nodes g (targetFace.toOrderHom i) := by
  have h0 : laurentNode g (InputSeedEvaluationNullUnit.unitNodes X 2) =
      InputSeedUnitNodes.lower g 6 :=
    (congrArg (laurentNode g) (InputSeedEvaluationNullUnit.lower_nodes X 1).symm).trans
      ((InputChartReference.pre_nodes g plus GlobalRawBass.plus_projection 1).symm.trans
        (InputSeedCornerNodes.pre_total g).symm)
  fin_cases i
  · exact h0
  · change laurentNode g (InputSeedEvaluationNullUnit.unitNodes X 3) =
      ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g)
        (InputSeedUnitNodes.lower g 6)
    exact (congrArg (laurentNode g) (InputSeedEvaluationNullUnit.upper_nodes X 1).symm).trans
      ((laurent_shift g (InputChartSimplex.nodes X 1)).symm.trans
        (congrArg (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g))
          ((congrArg (laurentNode g) (InputSeedEvaluationNullUnit.lower_nodes X 1)).trans h0)))

/-- The entire original raw unit agrees before native evaluation. -/
theorem newUnit (s : I) :
    InputSeedStrictMap.map g (InputSeedEvaluationNullUnit.newUnit X s) =
      InputSeedEvalRails.unitPath g 0 s := by
  change InputSeedStrictMap.map g
    (CutOpenCarrier.laurentInclusion _ _ _ _ _
      (parameter (InputSeedEvaluationCarrier.laurentRef X)
        (InputSeedEvaluationNullUnit.unitNodes X) (edge (k := 3) 2 3 s))) =
    CutOpenCarrier.laurentInclusion _ _ _ _ _ (InputSeedEvaluationProduct.parameter g (0, s))
  rw [InputSeedStrictMap.map_laurent, InputSeedProductRails.source]
  change CutOpenCarrier.laurentInclusion _ _ _ _ _
    (mapParameter (laurentNode g) (parameter _ _ (edge (k := 3) 2 3 s))) = _
  rw [mapParameter_parameter]
  congr 1
  have h := parameter_eq_of_face_nodes (InputSeedCarrier.laurentRef g)
    (InputSeedUnitNodes.nodes g)
    (fun i => laurentNode g (InputSeedEvaluationNullUnit.unitNodes X i))
    targetFace sourceFace (unit_nodes g) (edge (k := 1) 0 1 s)
  have hs : StdSimplex.map sourceFace.toOrderHom (edge (k := 1) 0 1 s) =
      edge (k := 3) 2 3 s := map_edge sourceFace 0 1 s
  have ht : StdSimplex.map targetFace.toOrderHom (edge (k := 1) 0 1 s) =
      edge (k := 15) 6 14 s := map_edge targetFace 0 1 s
  rw [hs, ht] at h
  exact h

/-- The whole shared D word retains both original binary nulls and the exact raw unit. -/
theorem word (s : I) : InputSeedStrictFace.targetParameter g s =
    InputSeedEvalFace.word g 0 s :=
  Path.Evaluation.path_trans (InputSeedStrictMap.map g)
    (InputSeedEvaluationNull.newNull X false).symm
    ((InputSeedEvaluationNullUnit.newUnit X).trans (InputSeedEvaluationNull.newNull X true))
    (InputSeedEvalNull.path g false 0).symm
    ((InputSeedEvalRails.unitPath g 0).trans (InputSeedEvalNull.path g true 0))
    (Path.Evaluation.path_symm (InputSeedStrictMap.map g)
      (InputSeedEvaluationNull.newNull X false) (InputSeedEvalNull.path g false 0)
      (newNull g false))
    (Path.Evaluation.path_trans (InputSeedStrictMap.map g)
      (InputSeedEvaluationNullUnit.newUnit X) (InputSeedEvaluationNull.newNull X true)
      (InputSeedEvalRails.unitPath g 0) (InputSeedEvalNull.path g true 0)
      (newUnit g) (newNull g true)) s

/-- The prescribed short-route faces share their entire original middle seed word. -/
theorem face (s : I) : InputSeedStrictFace.parameter g (1, s) =
    InputSeedEvalFace.parameter g (0, s) :=
  (InputSeedStrictFace.target g s).trans
    ((word g s).trans (InputSeedEvalFace.source g s).symm)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedStrictTargetSeam
