/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedPostMap
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedPostRows
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvaluationNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedInputNullParam
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartFaceSeams

/-!
# The full source null of raw-post evaluation

Actual raw pullback sends the original source evaluation null to the entire three-piece
input target word. Its raw-square half and target cone half retain their original clocks.
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
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedPostNullSeams
open GlobalSectionChangeIndex CommonReferenceNerve

private theorem parameter_single_eq {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) {p q : ℕ}
    (N : Fin (p + 1) → Node F) (M : Fin (q + 1) → Node F)
    (i : Fin (p + 1)) (j : Fin (q + 1)) (h : N i = M j) :
    parameter F N (StdSimplex.single i) = parameter F M (StdSimplex.single j) := by
  let α : ⦋0⦌ ⟶ ⦋p⦌ := SimplexCategory.Hom.mk ⟨fun _ ↦ i, fun _ _ _ ↦ le_rfl⟩
  let β : ⦋0⦌ ⟶ ⦋q⦌ := SimplexCategory.Hom.mk ⟨fun _ ↦ j, fun _ _ _ ↦ le_rfl⟩
  have e := parameter_eq_of_face_nodes F M N β α (fun _ ↦ h) (StdSimplex.single 0)
  rw [StdSimplex.map_single, StdSimplex.map_single] at e
  exact e

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Every finite Laurent parameter keeps its full shifted reference after raw input. -/
theorem sheet_parameter (e : Bool) {k : ℕ}
    (N : Fin (k + 1) → Node (InputSeedEvaluationCarrier.laurentRef Y))
    (z : StdSimplex ℝ (Fin (k + 1))) :
    InputSeedPostMap.map g
      (CutOpenCarrier.laurentInclusion
        (InputSeedEvaluationCarrier.polyRef Y) (InputSeedEvaluationCarrier.chart Y)
        (InputSeedEvaluationCarrier.laurentRef Y) (InputSeedEvaluationCarrier.ordinary Y)
        (InputSeedEvaluationCarrier.shifted Y)
        (if e then mapParameter
          (ModelSimplex.reanchorNode (InputSeedEvaluationCarrier.commonUnit Y))
            (parameter (InputSeedEvaluationCarrier.laurentRef Y) N z)
        else parameter (InputSeedEvaluationCarrier.laurentRef Y) N z)) =
      InputSeedInputNull.sheet g e
        (mapParameter (InputMixedDesc.postNode g)
          (parameter (InputSeedEvaluationCarrier.laurentRef Y) N z)) := by
  rw [InputSeedPostMap.map_laurent]
  cases e
  · rfl
  · change CutOpenCarrier.laurentInclusion _ _ _ _ _
      (mapParameter (InputMixedDesc.postNode g) (mapParameter
        (ModelSimplex.reanchorNode (InputSeedEvaluationCarrier.commonUnit Y))
          (parameter _ N z))) =
        CutOpenCarrier.laurentInclusion _ _ _ _ _
          (mapParameter (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g))
            (mapParameter (InputMixedDesc.postNode g) (parameter _ N z)))
    congr 1
    rw [mapParameter_parameter, mapParameter_parameter,
      mapParameter_parameter, mapParameter_parameter]
    exact congrArg (fun M => parameter (InputSeedCarrier.laurentRef g) M z)
      (funext fun i => (InputSeedPostUnit.post_shift g (N i)).symm)

/-- The complete original evaluation edge is the prescribed postcomposed chart edge. -/
theorem positiveMovement (e : Bool) (s : I) :
    InputSeedPostMap.map g (InputSeedEvaluationNullChart.positiveMovement Y e s) =
      InputSeedInputNull.edge g e 3 4 s := by
  have hs : InputSeedPostMap.map g
      (InputSeedEvaluationNullChart.positiveMovement Y e s) =
        InputSeedInputNull.sheet g e
          (mapParameter (InputMixedDesc.postNode g)
            (parameter (InputSeedEvaluationCarrier.laurentRef Y)
              (InputChartSimplex.nodes Y) (edge (k := 7) 0 3 s))) := by
    have h := sheet_parameter g e (InputChartSimplex.nodes Y) (edge (k := 7) 0 3 s)
    cases e <;> exact h
  have h := InputChartReference.plus_post_parameter g (edge (k := 4) 0 3 s)
  have hm : StdSimplex.map InputChartSimplex.plusFace.toOrderHom
      (edge (k := 4) 0 3 s) = edge (k := 7) 0 3 s :=
    map_edge InputChartSimplex.plusFace 0 3 s
  rw [hm] at h
  exact hs.trans (congrArg (InputSeedInputNull.sheet g e)
    (h.symm.trans (InputChartFaceSeams.post_edge g plus GlobalRawBass.plus_projection s).symm))

/-- The source polynomial node becomes precisely the terminal original projection cut. -/
theorem polynomial_zero :
    InputSeedPostMap.polynomialMap g (InputSeedEvaluationCarrier.movement Y 0) =
      InputSeedInputNull.polynomialEdge g 1 := by
  change mapParameter (InputSeedPostNodes.polynomialNode g)
    (parameter (InputSeedEvaluationCarrier.polyRef Y)
      (InputSeedEvaluationCarrier.polynomialNodes Y) (edge (k := 1) 0 1 0)) =
    parameter (InputSeedCarrier.polyRef g) (InputSpanParameterNodes.projectionNodes g)
      (edge (k := 7) 0 3 1)
  rw [mapParameter_parameter, (edge (k := 1) 0 1).source, (edge (k := 7) 0 3).target]
  exact parameter_single_eq (InputSeedCarrier.polyRef g)
    (fun i => InputSeedPostNodes.polynomialNode g (InputSeedEvaluationCarrier.polynomialNodes Y i))
    (InputSpanParameterNodes.projectionNodes g) 0 3 (InputSeedPostNodes.polynomial_zero g)

/-- The whole first image-cylinder half is the original reverse/forward raw chart word. -/
theorem rawHalf (e : Bool) (s : I) :
    InputSeedPostMap.rawHalf g e (s, InputSeedEvaluationCarrier.movement Y 0) =
      InputSeedInputNull.rawPath g e s := by
  have h := congrArg (InputSeedInputNull.sheet g e)
    (InputSeedPostRows.initial_parameter g s)
  change InputSeedInputNull.sheet g e
      (InputSeedPostProduct.parameter g (InputSeedEvaluationCarrier.movement Y 0, s)) =
    (((((InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection 1 2).trans
      (InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection 2 4)).symm).trans
      ((InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection 1 5).trans
        (InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection 5 7))).map
          (InputSeedInputNull.sheet g e).continuous) s at h
  have h' : InputSeedPostMap.rawHalf g e (s, InputSeedEvaluationCarrier.movement Y 0) =
      InputSeedInputNull.sheet g e
        (InputSeedPostProduct.parameter g (InputSeedEvaluationCarrier.movement Y 0, s)) := by
    cases e <;> rfl
  exact h'.trans (by
    simpa only [Path.map_trans, ← Path.map_symm, InputSeedInputNull.edge,
      InputSeedInputNull.rawPath] using h)

/-- The full second cylinder half has the original polynomial point and its unchanged height. -/
theorem targetCylinder (e : Bool) (s : I) :
    InputSeedPostMap.targetCylinder g e (s, InputSeedEvaluationCarrier.movement Y 0) =
      InputSeedInputNull.targetCylinder g e s := by
  cases e
  · change CutOpenCarrier.cylinderMinus _ _ _ _ _
      (InputSeedPostMap.polynomialMap g (InputSeedEvaluationCarrier.movement Y 0), s) = _
    rw [polynomial_zero]; rfl
  · change CutOpenCarrier.cylinderPlus _ _ _ _ _
      (InputSeedPostMap.polynomialMap g (InputSeedEvaluationCarrier.movement Y 0), s) = _
    rw [polynomial_zero]; rfl

/-- The original cone image retains both its raw-square half and its terminal cone half. -/
theorem oldCone (e : Bool) (s : I) :
    InputSeedPostMap.map g (InputSeedEvaluationNullChart.oldCone Y e s) =
      ((InputSeedInputNull.rawPath g e).trans (InputSeedInputNull.targetCylinder g e)) s := by
  have h : InputSeedPostMap.map g (InputSeedEvaluationNullChart.oldCone Y e s) =
      ((InputSeedPostMap.rawHalf g e).trans (InputSeedPostMap.targetCylinder g e))
        (s, InputSeedEvaluationCarrier.movement Y 0) := by
    cases e
    · exact InputSeedPostMap.map_cylinderMinus g _ s
    · exact InputSeedPostMap.map_cylinderPlus g _ s
  rw [h, ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split
  · exact rawHalf g e _
  · exact targetCylinder g e _

/-- The whole original old null becomes the prescribed three-piece input target null. -/
theorem oldNull (e : Bool) (s : I) :
    InputSeedPostMap.map g (InputSeedEvaluationNull.oldNull Y e s) =
      InputSeedInputNull.targetPath g e s :=
  Path.Evaluation.path_trans (InputSeedPostMap.map g)
    (InputSeedEvaluationNullChart.positiveMovement Y e) (InputSeedEvaluationNullChart.oldCone Y e)
    (InputSeedInputNull.edge g e 3 4)
    ((InputSeedInputNull.rawPath g e).trans (InputSeedInputNull.targetCylinder g e))
    (positiveMovement g e) (oldCone g e) s

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedPostNullSeams
