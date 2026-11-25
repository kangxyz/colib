/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedStrictNodes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedStrictMap
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvaluationNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedInputNullParam
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartFaceSeams

/-!
# Whole original source-null joins for strict input

Both sheets retain their original full Laurent references and actual polynomial cylinders.
The complete old-null word is identified before native evaluation, without cancelling a chart
map or replacing either original path clock.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity Topology
open CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedStrictNullSeams
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

private theorem map_parameter_commutation
    {V W T U : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    {F : V ⟶ W} {G : T ⟶ U} (f : Node F → Node G)
    (a : Node F → Node F) (b : Node G → Node G)
    (h : ∀ y, f (a y) = b (f y)) {k : ℕ} (N : Fin (k + 1) → Node F)
    (z : StdSimplex ℝ (Fin (k + 1))) :
    mapParameter f (mapParameter a (parameter F N z)) =
      mapParameter b (mapParameter f (parameter F N z)) := by
  simp only [mapParameter_parameter]
  exact congrArg (fun M ↦ parameter G M z) (funext fun i ↦ h (N i))

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Every original finite Laurent parameter keeps its full shifted reference after strict input. -/
theorem sheet_parameter (e : Bool) {k : ℕ}
    (N : Fin (k + 1) → Node (InputSeedEvaluationCarrier.laurentRef X))
    (z : StdSimplex ℝ (Fin (k + 1))) :
    InputSeedStrictMap.map g
      (CutOpenCarrier.laurentInclusion
        (InputSeedEvaluationCarrier.polyRef X) (InputSeedEvaluationCarrier.chart X)
        (InputSeedEvaluationCarrier.laurentRef X) (InputSeedEvaluationCarrier.ordinary X)
        (InputSeedEvaluationCarrier.shifted X)
        (if e then mapParameter
          (ModelSimplex.reanchorNode (InputSeedEvaluationCarrier.commonUnit X))
            (parameter (InputSeedEvaluationCarrier.laurentRef X) N z)
        else parameter (InputSeedEvaluationCarrier.laurentRef X) N z)) =
      InputSeedInputNull.sheet g e
        (mapParameter (laurentNode g)
          (parameter (InputSeedEvaluationCarrier.laurentRef X) N z)) := by
  rw [InputSeedStrictMap.map_laurent]
  cases e
  · rfl
  · change CutOpenCarrier.laurentInclusion _ _ _ _ _
      (mapParameter (laurentNode g) (mapParameter
        (ModelSimplex.reanchorNode (InputSeedEvaluationCarrier.commonUnit X))
          (parameter _ N z))) =
        CutOpenCarrier.laurentInclusion _ _ _ _ _
          (mapParameter (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g))
            (mapParameter (laurentNode g) (parameter _ N z)))
    congr 1
    exact map_parameter_commutation (laurentNode g)
      (ModelSimplex.reanchorNode (InputSeedEvaluationCarrier.commonUnit X))
      (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g))
      (fun y ↦ (laurent_shift g y).symm) N z

/-- The actual positive evaluation edge is the full original source chart edge on either sheet. -/
theorem positiveMovement (e : Bool) (s : I) :
    InputSeedStrictMap.map g (InputSeedEvaluationNullChart.positiveMovement X e s) =
      InputSeedInputNull.edge g e 0 6 s := by
  have hs : InputSeedStrictMap.map g
      (InputSeedEvaluationNullChart.positiveMovement X e s) =
        InputSeedInputNull.sheet g e
          (mapParameter (laurentNode g)
            (parameter (InputSeedEvaluationCarrier.laurentRef X)
              (InputChartSimplex.nodes X) (edge (k := 7) 0 3 s))) := by
    have h := sheet_parameter g e (InputChartSimplex.nodes X) (edge (k := 7) 0 3 s)
    cases e <;> exact h
  have h := InputChartReference.plus_pre_parameter g (edge (k := 4) 0 3 s)
  have hm : StdSimplex.map InputChartSimplex.plusFace.toOrderHom
      (edge (k := 4) 0 3 s) = edge (k := 7) 0 3 s :=
    map_edge InputChartSimplex.plusFace 0 3 s
  rw [hm] at h
  exact hs.trans (congrArg (InputSeedInputNull.sheet g e)
    (h.symm.trans (InputChartFaceSeams.pre_edge g plus GlobalRawBass.plus_projection s).symm))

/-- The source polynomial parameter is the same complete original projection node. -/
theorem polynomial_zero :
    InputSeedStrictMap.polynomialMap g (InputSeedEvaluationCarrier.movement X 0) =
      InputSeedInputNull.polynomialEdge g 0 := by
  change mapParameter (polynomialNode g)
    (parameter (InputSeedEvaluationCarrier.polyRef X)
      (InputSeedEvaluationCarrier.polynomialNodes X) (edge (k := 1) 0 1 0)) =
    parameter (InputSeedCarrier.polyRef g) (InputSpanParameterNodes.projectionNodes g)
      (edge (k := 7) 0 3 0)
  rw [mapParameter_parameter, (edge (k := 1) 0 1).source, (edge (k := 7) 0 3).source]
  exact parameter_single_eq (InputSeedCarrier.polyRef g)
    (fun i ↦ polynomialNode g (InputSeedEvaluationCarrier.polynomialNodes X i))
    (InputSpanParameterNodes.projectionNodes g) 0 0 (InputSeedStrictNodes.polynomial_zero g)

/-- The unchanged cylinder preserves its exact height and its own tip. -/
theorem oldCone (e : Bool) (s : I) :
    InputSeedStrictMap.map g (InputSeedEvaluationNullChart.oldCone X e s) =
      InputSeedInputNull.sourceCylinder g e s := by
  cases e
  · change InputSeedStrictMap.map g (CutOpenCarrier.cylinderMinus _ _ _ _ _
      (InputSeedEvaluationCarrier.movement X 0, s)) = _
    rw [InputSeedStrictMap.map_cylinderMinus, polynomial_zero]
    rfl
  · change InputSeedStrictMap.map g (CutOpenCarrier.cylinderPlus _ _ _ _ _
      (InputSeedEvaluationCarrier.movement X 0, s)) = _
    rw [InputSeedStrictMap.map_cylinderPlus, polynomial_zero]
    rfl

/-- The entire old null retains its original positive half and actual cylinder half. -/
theorem oldNull (e : Bool) (s : I) :
    InputSeedStrictMap.map g (InputSeedEvaluationNull.oldNull X e s) =
      InputSeedInputNull.sourcePath g e s :=
  Path.Evaluation.path_trans (InputSeedStrictMap.map g)
    (InputSeedEvaluationNullChart.positiveMovement X e)
    (InputSeedEvaluationNullChart.oldCone X e)
    (InputSeedInputNull.edge g e 0 6) (InputSeedInputNull.sourceCylinder g e)
    (positiveMovement g e) (oldCone g e) s

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedStrictNullSeams
