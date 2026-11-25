/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedTransitionFace
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvalBinaryEnds
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvalFace

/-!
# The whole common terminal word of raw transition and moving evaluation

The original raw normalization row, its terminal polynomial node, and its complete unit
references agree in the mixed carrier. Both null sheets and the final raw unit retain every
original parameter before native evaluation.
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
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedRawTargetSeam
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedRawUnit

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
  exact congrArg (fun M => parameter G M z) (funext fun i => h (N i))

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Every finite original raw Laurent family retains its separately shifted full reference. -/
theorem sheet_parameter (e : Bool) {k : ℕ}
    (N : Fin (k + 1) → Node (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g))
    (z : StdSimplex ℝ (Fin (k + 1))) :
    InputSeedRawMap.map g
      (CutOpenCarrier.laurentInclusion
        (GlobalRawBass.InputIdentitySeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
        (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g)
        (GlobalRawBass.InputIdentitySeedCarrier.ordinary g)
        (GlobalRawBass.InputIdentitySeedCarrier.shifted g)
        (if e then mapParameter
          (ModelSimplex.reanchorNode (GlobalRawBass.InputIdentitySeedCarrier.commonUnit g))
            (parameter (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g) N z)
        else parameter (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g) N z)) =
      InputSeedInputNull.sheet g e
        (mapParameter (evaluateNode g)
          (parameter (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g) N z)) := by
  rw [InputSeedRawMap.map_laurent]
  cases e
  · rfl
  · change CutOpenCarrier.laurentInclusion _ _ _ _ _
      (mapParameter (evaluateNode g) (mapParameter
        (ModelSimplex.reanchorNode (rawUnit g)) (parameter _ N z))) =
        CutOpenCarrier.laurentInclusion _ _ _ _ _
          (mapParameter (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g))
            (mapParameter (evaluateNode g) (parameter _ N z)))
    congr 1
    exact map_parameter_commutation (evaluateNode g)
      (ModelSimplex.reanchorNode (rawUnit g))
      (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g))
      (fun y => (evaluate_shift g y).symm) N z

/-- The complete original raw positive chart face retains all eighteen dependent nodes. -/
theorem positive_parameter (z : StdSimplex ℝ (Fin 18)) :
    mapParameter (evaluateNode g)
      (parameter (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g)
        (GlobalRawBass.InputDescSimplex.nodes g)
        (StdSimplex.map BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom z)) =
      parameter (InputSeedCarrier.laurentRef g)
        (InputChartReference.rawNode g plus GlobalRawBass.plus_projection) z := by
  rw [mapParameter_parameter, parameter_face]
  exact congrArg (fun M => parameter (InputSeedCarrier.laurentRef g) M z)
    (funext fun i => (congrArg (evaluateNode g)
      (GlobalRawBass.InputDescSimplex.plus_nodes g i)).trans
        (InputRawDesc.chart_node g plus
          GlobalRawBass.plus_projection i).symm)

/-- The entire terminal normalization row is the original raw binary path. -/
theorem binary_parameter (s : unitInterval) :
    mapParameter (evaluateNode g)
      (parameter (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g)
        (GlobalRawBass.InputDescSimplex.nodes g)
        (BoundedFlatPerfectProjectionRectangleParameters.K
          BoundedFlatCoefficientBassH0Diagram.plusFace s)) =
      InputSeedEvalBinary.parameter g (1, s) := by
  have h₀ : StdSimplex.map InputRectangleNodes.preNormalizationFace.toOrderHom
      (binaryPath (k := 2) 0 1 2 s) = binaryPath (k := 17) 15 16 17 s :=
    map_binaryPath InputRectangleNodes.preNormalizationFace 0 1 2 s
  have h₁ : StdSimplex.map BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom
      (binaryPath (k := 17) 15 16 17 s) =
      BoundedFlatPerfectProjectionRectangleParameters.K
        BoundedFlatCoefficientBassH0Diagram.plusFace s :=
    map_binaryPath BoundedFlatCoefficientBassH0Diagram.plusFace 15 16 17 s
  rw [← h₁, positive_parameter, InputSeedEvalBinary.target_parameter, h₀]

/-- Both actual raw positive binary paths agree before either native sheet evaluation. -/
theorem newPositive (e : Bool) (s : unitInterval) :
    InputSeedRawMap.map g (GlobalRawBass.InputIdentitySeedRectangle.newPositive g e s) =
      InputSeedEvalNull.binarySwap g e (s, 1) := by
  have hs := sheet_parameter g e (GlobalRawBass.InputDescSimplex.nodes g)
    (BoundedFlatPerfectProjectionRectangleParameters.K
      BoundedFlatCoefficientBassH0Diagram.plusFace s)
  have h : InputSeedRawMap.map g
      (GlobalRawBass.InputIdentitySeedRectangle.newPositive g e s) =
      InputSeedInputNull.sheet g e
        (mapParameter (evaluateNode g)
          (parameter (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g)
            (GlobalRawBass.InputDescSimplex.nodes g)
            (BoundedFlatPerfectProjectionRectangleParameters.K
              BoundedFlatCoefficientBassH0Diagram.plusFace s))) := by
    cases e <;> exact hs
  exact h.trans (congrArg (InputSeedInputNull.sheet g e) (binary_parameter g s))

/-- The actual raw polynomial endpoint is the whole seventh projection node. -/
theorem polynomial_one : InputSeedRawMap.polynomialMap g
    (GlobalRawBass.InputIdentitySeedCarrier.movement g 1) =
      InputSeedEvalBinary.polynomialParameter g 1 := by
  change mapParameter (InputSeedRawAttachment.polynomialNode g)
    (parameter (GlobalRawBass.InputIdentitySeedCarrier.polyRef g)
      (GlobalRawBass.InputIdentitySeedCarrier.polynomialNodes g)
      (BoundedFlatPerfectNativeSquareFiveSimplex.parameter 1)) = _
  rw [Path.target, mapParameter_parameter, InputSeedEvalBinary.polynomial_target]
  exact parameter_single_eq (InputSeedCarrier.polyRef g)
    (fun i => InputSeedRawAttachment.polynomialNode g
      (GlobalRawBass.InputIdentitySeedCarrier.polynomialNodes g i))
    (InputSpanParameterNodes.projectionNodes g) 4 7
    (InputChartNormalizationNodes.commuting_normalization_nodes (polynomial.map g)
      (projection.app Y)
      (projection.app X) g (projection.naturality g) 4).symm

/-- The entire last cone cylinder keeps its original height on each separate sheet. -/
theorem newCone (e : Bool) (s : unitInterval) :
    InputSeedRawMap.map g (GlobalRawBass.InputIdentitySeedRectangle.newCone g e s) =
      InputSeedEvalNull.cylinderSwap g e (s, 1) := by
  cases e
  · change InputSeedRawMap.map g
      (CutOpenCarrier.cylinderMinus _ (InputSeedCarrier.chart (X := X)) _ _ _
      (GlobalRawBass.InputIdentitySeedCarrier.movement g 1, s)) = _
    rw [InputSeedRawMap.map_cylinderMinus, polynomial_one]
    rfl
  · change InputSeedRawMap.map g
      (CutOpenCarrier.cylinderPlus _ (InputSeedCarrier.chart (X := X)) _ _ _
      (GlobalRawBass.InputIdentitySeedCarrier.movement g 1, s)) = _
    rw [InputSeedRawMap.map_cylinderPlus, polynomial_one]
    rfl

/-- Both original final null words retain the prescribed binary and cylinder half clocks. -/
theorem newNull (e : Bool) (s : unitInterval) :
    InputSeedRawMap.map g (GlobalRawBass.InputIdentitySeedNull.newNull g e s) =
      InputSeedEvalNull.path g e 1 s := by
  change InputSeedRawMap.map g
    (((GlobalRawBass.InputIdentitySeedRectangle.newPositive g e).trans
      (GlobalRawBass.InputIdentitySeedRectangle.newCone g e)) s) =
    ((InputSeedEvalNull.binarySwap g e).trans (InputSeedEvalNull.cylinderSwap g e)) (s, 1)
  rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split
  · exact newPositive g e _
  · exact newCone g e _

private def sourceFace : ⦋1⦌ ⟶ ⦋9⦌ := SimplexCategory.Hom.mk ⟨![4, 9], by decide⟩
private def targetFace : ⦋1⦌ ⟶ ⦋15⦌ := SimplexCategory.Hom.mk ⟨![7, 15], by decide⟩

/-- Both full final unit nodes agree with the unchanged terminal product column. -/
private theorem unit_nodes (i : Fin 2) :
    evaluateNode g (GlobalRawBass.InputIdentitySeedUnitNodes.nodes g
      (sourceFace.toOrderHom i)) =
      InputSeedUnitNodes.nodes g (targetFace.toOrderHom i) := by
  have h0 : evaluateNode g (GlobalRawBass.InputIdentitySeedUnitNodes.nodes g 4) =
      InputSeedUnitNodes.lower g 7 :=
    (congrArg (evaluateNode g)
      (GlobalRawBass.InputIdentitySeedUnitSeams.outer_nodes g 4).symm).trans
      ((congrArg (evaluateNode g)
        (GlobalRawBass.InputDescSimplex.plus_nodes g 15)).trans
        ((InputRawDesc.chart_node g plus
          GlobalRawBass.plus_projection 15).symm.trans
          (InputSeedCornerNodes.target_raw g).symm))
  fin_cases i
  · exact h0
  · change evaluateNode g (GlobalRawBass.InputIdentitySeedUnitNodes.nodes g 9) =
      ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g)
        (InputSeedUnitNodes.lower g 7)
    exact (congrArg (evaluateNode g)
      (GlobalRawBass.InputIdentitySeedUnitSeams.five_shift g 4).symm).trans
      ((evaluate_shift g _).symm.trans
        (congrArg (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g)) h0))

/-- The whole final raw unit agrees before native evaluation at every unit time. -/
theorem newUnit (s : unitInterval) :
    InputSeedRawMap.map g (GlobalRawBass.InputIdentitySeedConjugation.newUnit g s) =
      InputSeedEvalRails.unitPath g 1 s := by
  change InputSeedRawMap.map g
    (CutOpenCarrier.laurentInclusion _ (InputSeedCarrier.chart (X := X)) _ _ _
      (parameter (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g)
        (GlobalRawBass.InputIdentitySeedUnitNodes.nodes g) (edge (k := 9) 4 9 s))) =
    CutOpenCarrier.laurentInclusion _ _ _ _ _ (InputSeedEvaluationProduct.parameter g (1, s))
  rw [InputSeedRawMap.map_laurent, InputSeedProductRails.target]
  change CutOpenCarrier.laurentInclusion _ _ _ _ _
    (mapParameter (evaluateNode g) (parameter _ _ (edge (k := 9) 4 9 s))) = _
  rw [mapParameter_parameter]
  congr 1
  have h := parameter_eq_of_face_nodes (InputSeedCarrier.laurentRef g)
    (InputSeedUnitNodes.nodes g)
    (fun i => evaluateNode g (GlobalRawBass.InputIdentitySeedUnitNodes.nodes g i))
    targetFace sourceFace (unit_nodes g) (edge (k := 1) 0 1 s)
  have hs : StdSimplex.map sourceFace.toOrderHom (edge (k := 1) 0 1 s) =
      edge (k := 9) 4 9 s := map_edge sourceFace 0 1 s
  have ht : StdSimplex.map targetFace.toOrderHom (edge (k := 1) 0 1 s) =
      edge (k := 15) 7 15 s := map_edge targetFace 0 1 s
  rw [hs, ht] at h
  exact h

/-- The complete original final seed word agrees on both routes. -/
theorem word (s : unitInterval) : InputSeedTransitionFace.targetParameter g s =
    InputSeedEvalFace.word g 1 s :=
  Path.Evaluation.path_trans (InputSeedRawMap.map g)
    (GlobalRawBass.InputIdentitySeedNull.newNull g false).symm
    ((GlobalRawBass.InputIdentitySeedConjugation.newUnit g).trans
      (GlobalRawBass.InputIdentitySeedNull.newNull g true))
    (InputSeedEvalNull.path g false 1).symm
    ((InputSeedEvalRails.unitPath g 1).trans (InputSeedEvalNull.path g true 1))
    (Path.Evaluation.path_symm (InputSeedRawMap.map g)
      (GlobalRawBass.InputIdentitySeedNull.newNull g false) (InputSeedEvalNull.path g false 1)
      (newNull g false))
    (Path.Evaluation.path_trans (InputSeedRawMap.map g)
      (GlobalRawBass.InputIdentitySeedConjugation.newUnit g)
      (GlobalRawBass.InputIdentitySeedNull.newNull g true)
      (InputSeedEvalRails.unitPath g 1) (InputSeedEvalNull.path g true 1)
      (newUnit g) (newNull g true)) s

/-- The prescribed long and short route faces meet on their entire terminal seed word. -/
theorem face (s : unitInterval) : InputSeedTransitionFace.parameter g (1, s) =
    InputSeedEvalFace.parameter g (1, s) :=
  (InputSeedTransitionFace.target g s).trans
    ((word g s).trans (InputSeedEvalFace.target g s).symm)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedRawTargetSeam
