/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedPostNullSeams
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedPostFace
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedRawTargetSeam

/-!
# The whole join from postcomposed evaluation to original raw transition

The postcomposed binary rail, the terminal product row, the polynomial cylinder and both unit
references agree in the same actual carrier. Their unchanged nested words give the entire
shared intermediate seed path.
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
universe u v w z
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedPostTargetSeam
open GlobalSectionChangeIndex CommonReferenceNerve

private theorem two_maps_trans {A : Type v} {B : Type w} {T : Type z}
    [TopologicalSpace A] [TopologicalSpace B]
    (f : A → T) (g : B → T) {a b c : A} {d e k : B}
    (P : Path a b) (Q : Path b c) (R : Path d e) (S : Path e k)
    (hP : ∀ s, f (P s) = g (R s)) (hQ : ∀ s, f (Q s) = g (S s)) (s : I) :
    f ((P.trans Q) s) = g ((R.trans S) s) := by
  rw [Path.trans_apply, Path.trans_apply]
  split
  · exact hP _
  · exact hQ _

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

/-- The entire postcomposed old binary agrees with the original raw rectangle source binary. -/
theorem binary_parameter (s : I) :
    mapParameter (InputMixedDesc.postNode g)
      (parameter (InputSeedEvaluationCarrier.laurentRef Y) (InputChartSimplex.nodes Y)
        (binaryPath (k := 7) 1 2 4 s)) =
    mapParameter (InputSeedRawUnit.evaluateNode g)
      (parameter (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g)
        (GlobalRawBass.InputDescSimplex.nodes g)
        (BoundedFlatPerfectProjectionRectangleParameters.D
          BoundedFlatCoefficientBassH0Diagram.plusFace s)) := by
  have hp := InputChartReference.plus_post_parameter g (binaryPath (k := 4) 1 2 4 s)
  have hp' : StdSimplex.map InputChartSimplex.plusFace.toOrderHom
      (binaryPath (k := 4) 1 2 4 s) = binaryPath (k := 7) 1 2 4 s :=
    map_binaryPath InputChartSimplex.plusFace 1 2 4 s
  rw [hp'] at hp
  have hn := InputChartReference.normalization_parameter g plus GlobalRawBass.plus_projection
    (binaryPath (k := 2) 0 1 2 s)
  have hn₀ : StdSimplex.map
      (InputSimplex.triangleFace 1 2 4 (by decide) (by decide)).toOrderHom
      (binaryPath (k := 2) 0 1 2 s) = binaryPath (k := 4) 1 2 4 s :=
    map_binaryPath (InputSimplex.triangleFace 1 2 4 (by decide) (by decide)) 0 1 2 s
  have hn₁ : StdSimplex.map InputRectangleNodes.normalizationFace.toOrderHom
      (binaryPath (k := 2) 0 1 2 s) = binaryPath (k := 17) 2 3 11 s :=
    map_binaryPath InputRectangleNodes.normalizationFace 0 1 2 s
  rw [hn₀, hn₁] at hn
  have he : StdSimplex.map BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom
      (binaryPath (k := 17) 2 3 11 s) =
      BoundedFlatPerfectProjectionRectangleParameters.D
        BoundedFlatCoefficientBassH0Diagram.plusFace s :=
    map_binaryPath BoundedFlatCoefficientBassH0Diagram.plusFace 2 3 11 s
  rw [← he, InputSeedRawTargetSeam.positive_parameter]
  exact hp.symm.trans hn

/-- Each complete postcomposed positive binary keeps its original raw source word. -/
theorem newPositive (e : Bool) (s : I) :
    InputSeedPostMap.map g (InputSeedEvaluationNullChart.newPositive Y e s) =
      InputSeedRawMap.map g (GlobalRawBass.InputIdentitySeedRectangle.oldPositive g e s) := by
  have hp := InputSeedPostNullSeams.sheet_parameter g e (InputChartSimplex.nodes Y)
    (binaryPath (k := 7) 1 2 4 s)
  have hr := InputSeedRawTargetSeam.sheet_parameter g e (GlobalRawBass.InputDescSimplex.nodes g)
    (BoundedFlatPerfectProjectionRectangleParameters.D
      BoundedFlatCoefficientBassH0Diagram.plusFace s)
  have hp' : InputSeedPostMap.map g (InputSeedEvaluationNullChart.newPositive Y e s) =
      InputSeedInputNull.sheet g e
        (mapParameter (InputMixedDesc.postNode g)
          (parameter (InputSeedEvaluationCarrier.laurentRef Y) (InputChartSimplex.nodes Y)
            (binaryPath (k := 7) 1 2 4 s))) := by
    cases e <;> exact hp
  have hr' : InputSeedRawMap.map g
      (GlobalRawBass.InputIdentitySeedRectangle.oldPositive g e s) =
      InputSeedInputNull.sheet g e
        (mapParameter (InputSeedRawUnit.evaluateNode g)
          (parameter (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g)
            (GlobalRawBass.InputDescSimplex.nodes g)
            (BoundedFlatPerfectProjectionRectangleParameters.D
              BoundedFlatCoefficientBassH0Diagram.plusFace s))) := by
    cases e <;> exact hr
  exact hp'.trans ((congrArg (InputSeedInputNull.sheet g e) (binary_parameter g s)).trans hr'.symm)

/-- The entire terminal raw-product row is the original evaluated positive square. -/
theorem rawHalf (e : Bool) (s : I) :
    InputSeedPostMap.rawHalf g e (s, InputSeedEvaluationCarrier.movement Y 1) =
      InputSeedRawMap.map g (GlobalRawBass.InputIdentitySeedRectangle.positiveMovement g e s) := by
  have hp : InputSeedPostProduct.parameter g (InputSeedEvaluationCarrier.movement Y 1, s) =
      mapParameter (InputSeedRawUnit.evaluateNode g)
        (parameter (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g)
          (GlobalRawBass.InputDescSimplex.nodes g)
          (BoundedFlatPerfectProjectionRectangleParameters.L
            BoundedFlatCoefficientBassH0Diagram.plusFace s)) := by
    rw [InputSeedPostRows.terminal_parameter]
    change parameter (InputSeedCarrier.laurentRef g) (InputRawDesc.nodes g)
      (BoundedFlatCoefficientBassH0Diagram.parameter (s, 0)) = _
    rw [BoundedFlatCoefficientBassH0Merged.h0_parameter_left, mapParameter_parameter]; rfl
  have hr := InputSeedRawTargetSeam.sheet_parameter g e (GlobalRawBass.InputDescSimplex.nodes g)
    (BoundedFlatPerfectProjectionRectangleParameters.L
      BoundedFlatCoefficientBassH0Diagram.plusFace s)
  have hr' : InputSeedRawMap.map g
      (GlobalRawBass.InputIdentitySeedRectangle.positiveMovement g e s) =
      InputSeedInputNull.sheet g e
        (mapParameter (InputSeedRawUnit.evaluateNode g)
          (parameter (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g)
            (GlobalRawBass.InputDescSimplex.nodes g)
            (BoundedFlatPerfectProjectionRectangleParameters.L
              BoundedFlatCoefficientBassH0Diagram.plusFace s))) := by
    cases e <;> exact hr
  have h : InputSeedPostMap.rawHalf g e (s, InputSeedEvaluationCarrier.movement Y 1) =
      InputSeedInputNull.sheet g e
        (InputSeedPostProduct.parameter g (InputSeedEvaluationCarrier.movement Y 1, s)) := by
    cases e <;> rfl
  exact h.trans ((congrArg (InputSeedInputNull.sheet g e) hp).trans hr'.symm)

/-- The two original polynomial routes share their complete fourth projection node. -/
theorem polynomial_one :
    InputSeedPostMap.polynomialMap g (InputSeedEvaluationCarrier.movement Y 1) =
      InputSeedRawMap.polynomialMap g (GlobalRawBass.InputIdentitySeedCarrier.movement g 0) := by
  change mapParameter (InputSeedPostNodes.polynomialNode g)
    (parameter (InputSeedEvaluationCarrier.polyRef Y)
      (InputSeedEvaluationCarrier.polynomialNodes Y) (edge (k := 1) 0 1 1)) =
    mapParameter (InputSeedRawAttachment.polynomialNode g)
      (parameter (GlobalRawBass.InputIdentitySeedCarrier.polyRef g)
        (GlobalRawBass.InputIdentitySeedCarrier.polynomialNodes g)
        (BoundedFlatPerfectNativeSquareFiveSimplex.parameter 0))
  rw [Path.target, Path.source, mapParameter_parameter, mapParameter_parameter]
  have hp := InputSeedPostNodes.polynomial_one g
  have hr := InputChartNormalizationNodes.commuting_normalization_nodes (polynomial.map g)
    (projection.app Y)
    (projection.app X) g (projection.naturality g) 2
  exact parameter_single_eq (InputSeedCarrier.polyRef g)
    (fun i => InputSeedPostNodes.polynomialNode g (InputSeedEvaluationCarrier.polynomialNodes Y i))
    (fun i => InputSeedRawAttachment.polynomialNode g
      (GlobalRawBass.InputIdentitySeedCarrier.polynomialNodes g i)) 1 2 (hp.trans hr)

/-- The whole target cylinder retains the original raw-source polynomial parameter and height. -/
theorem targetCylinder (e : Bool) (s : I) :
    InputSeedPostMap.targetCylinder g e (s, InputSeedEvaluationCarrier.movement Y 1) =
      InputSeedRawMap.map g (GlobalRawBass.InputIdentitySeedRectangle.oldCone g e s) := by
  cases e
  · change CutOpenCarrier.cylinderMinus _ _ _ _ _
      (InputSeedPostMap.polynomialMap g (InputSeedEvaluationCarrier.movement Y 1), s) =
      InputSeedRawMap.map g
      (CutOpenCarrier.cylinderMinus _ (InputSeedCarrier.chart (X := X)) _ _ _
        (GlobalRawBass.InputIdentitySeedCarrier.movement g 0, s))
    rw [InputSeedRawMap.map_cylinderMinus, polynomial_one]
  · change CutOpenCarrier.cylinderPlus _ _ _ _ _
      (InputSeedPostMap.polynomialMap g (InputSeedEvaluationCarrier.movement Y 1), s) =
      InputSeedRawMap.map g
      (CutOpenCarrier.cylinderPlus _ (InputSeedCarrier.chart (X := X)) _ _ _
        (GlobalRawBass.InputIdentitySeedCarrier.movement g 0, s))
    rw [InputSeedRawMap.map_cylinderPlus, polynomial_one]

/-- The entire image cone is precisely the original raw positive square followed by its cone. -/
theorem newCone (e : Bool) (s : I) :
    InputSeedPostMap.map g (InputSeedEvaluationNullChart.newCone Y e s) =
      InputSeedRawMap.map g
        (((GlobalRawBass.InputIdentitySeedRectangle.positiveMovement g e).trans
          (GlobalRawBass.InputIdentitySeedRectangle.oldCone g e)) s) := by
  have h : InputSeedPostMap.map g (InputSeedEvaluationNullChart.newCone Y e s) =
      ((InputSeedPostMap.rawHalf g e).trans (InputSeedPostMap.targetCylinder g e))
        (s, InputSeedEvaluationCarrier.movement Y 1) := by
    cases e
    · exact InputSeedPostMap.map_cylinderMinus g _ s
    · exact InputSeedPostMap.map_cylinderPlus g _ s
  rw [h, ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split
  · exact rawHalf g e _
  · exact targetCylinder g e _

/-- Both entire null words retain the original outer half and inner quarter cuts. -/
theorem newNull (e : Bool) (s : I) :
    InputSeedPostMap.map g (InputSeedEvaluationNull.newNull Y e s) =
      InputSeedRawMap.map g (GlobalRawBass.InputIdentitySeedNull.oldNull g e s) :=
  two_maps_trans (InputSeedPostMap.map g) (InputSeedRawMap.map g)
    (InputSeedEvaluationNullChart.newPositive Y e) (InputSeedEvaluationNullChart.newCone Y e)
    (GlobalRawBass.InputIdentitySeedRectangle.oldPositive g e)
    ((GlobalRawBass.InputIdentitySeedRectangle.positiveMovement g e).trans
      (GlobalRawBass.InputIdentitySeedRectangle.oldCone g e)) (newPositive g e) (newCone g e) s

private def postFace : ⦋1⦌ ⟶ ⦋3⦌ := SimplexCategory.Hom.mk ⟨![2, 3], by decide⟩
private def rawFace : ⦋1⦌ ⟶ ⦋9⦌ := SimplexCategory.Hom.mk ⟨![2, 7], by decide⟩

/-- Both complete unit endpoints agree through their actual common postcomposed total node. -/
private theorem unit_nodes (i : Fin 2) :
    InputMixedDesc.postNode g (InputSeedEvaluationNullUnit.unitNodes Y (postFace.toOrderHom i)) =
      InputSeedRawUnit.evaluateNode g
        (GlobalRawBass.InputIdentitySeedUnitNodes.nodes g (rawFace.toOrderHom i)) := by
  have hp : InputMixedDesc.postNode g (InputSeedEvaluationNullUnit.unitNodes Y 2) =
      InputSeedUnitNodes.lower g 4 :=
    (congrArg (InputMixedDesc.postNode g)
      (InputSeedEvaluationNullUnit.lower_nodes Y 1).symm).trans
      ((InputChartReference.post_nodes g plus GlobalRawBass.plus_projection 1).symm.trans
        (InputSeedCornerNodes.post_total g).symm)
  have hr : InputSeedRawUnit.evaluateNode g (GlobalRawBass.InputIdentitySeedUnitNodes.nodes g 2) =
      InputSeedUnitNodes.lower g 4 :=
    (congrArg (InputSeedRawUnit.evaluateNode g)
      (GlobalRawBass.InputIdentitySeedUnitSeams.outer_nodes g 2).symm).trans
      ((congrArg (InputSeedRawUnit.evaluateNode g)
        (GlobalRawBass.InputDescSimplex.plus_nodes g 2)).trans
        ((InputRawDesc.chart_node g plus
          GlobalRawBass.plus_projection 2).symm.trans (InputSeedCornerNodes.post_raw g).symm))
  have h0 := hp.trans hr.symm
  fin_cases i
  · exact h0
  · change InputMixedDesc.postNode g (InputSeedEvaluationNullUnit.unitNodes Y 3) =
      InputSeedRawUnit.evaluateNode g (GlobalRawBass.InputIdentitySeedUnitNodes.nodes g 7)
    have hp' := (congrArg (InputMixedDesc.postNode g)
      (InputSeedEvaluationNullUnit.upper_nodes Y 1).symm).trans
      (InputSeedPostUnit.post_shift g (InputChartSimplex.nodes Y 1)).symm
    have hr' := (InputSeedRawUnit.evaluate_shift g
      (GlobalRawBass.InputIdentitySeedUnitNodes.nodes g 2)).trans
      (congrArg (InputSeedRawUnit.evaluateNode g)
        (GlobalRawBass.InputIdentitySeedUnitSeams.five_shift g 2))
    exact hp'.trans ((congrArg (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g))
      ((congrArg (InputMixedDesc.postNode g) (InputSeedEvaluationNullUnit.lower_nodes Y 1)).trans
        h0)).trans hr')

/-- The entire intermediate unit path keeps both original anchors and its unchanged unit time. -/
theorem newUnit (s : I) :
    InputSeedPostMap.map g (InputSeedEvaluationNullUnit.newUnit Y s) =
      InputSeedRawMap.map g (GlobalRawBass.InputIdentitySeedConjugation.oldUnit g s) := by
  change InputSeedPostMap.map g
    (CutOpenCarrier.laurentInclusion _ _ _ _ _
      (parameter (InputSeedEvaluationCarrier.laurentRef Y)
        (InputSeedEvaluationNullUnit.unitNodes Y) (edge (k := 3) 2 3 s))) =
    InputSeedRawMap.map g
      (CutOpenCarrier.laurentInclusion _ (InputSeedCarrier.chart (X := X)) _ _ _
        (parameter (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g)
          (GlobalRawBass.InputIdentitySeedUnitNodes.nodes g) (edge (k := 9) 2 7 s)))
  rw [InputSeedPostMap.map_laurent, InputSeedRawMap.map_laurent]
  change CutOpenCarrier.laurentInclusion _ _ _ _ _
    (mapParameter (InputMixedDesc.postNode g) (parameter _ _ (edge (k := 3) 2 3 s))) =
    CutOpenCarrier.laurentInclusion _ _ _ _ _
      (mapParameter (InputSeedRawUnit.evaluateNode g) (parameter _ _ (edge (k := 9) 2 7 s)))
  rw [mapParameter_parameter, mapParameter_parameter]
  congr 1
  have h := parameter_eq_of_face_nodes (InputSeedCarrier.laurentRef g)
    (fun i => InputSeedRawUnit.evaluateNode g (GlobalRawBass.InputIdentitySeedUnitNodes.nodes g i))
    (fun i => InputMixedDesc.postNode g (InputSeedEvaluationNullUnit.unitNodes Y i))
    rawFace postFace (unit_nodes g) (edge (k := 1) 0 1 s)
  have hp : StdSimplex.map postFace.toOrderHom (edge (k := 1) 0 1 s) =
      edge (k := 3) 2 3 s := map_edge postFace 0 1 s
  have hr : StdSimplex.map rawFace.toOrderHom (edge (k := 1) 0 1 s) =
      edge (k := 9) 2 7 s := map_edge rawFace 0 1 s
  rw [hp, hr] at h
  exact h

/-- The whole common C word retains both original three-piece nulls and the exact unit. -/
theorem word (s : I) : InputSeedPostFace.targetParameter g s =
    InputSeedTransitionFace.sourceParameter g s :=
  two_maps_trans (InputSeedPostMap.map g) (InputSeedRawMap.map g)
    (InputSeedEvaluationNull.newNull Y false).symm
    ((InputSeedEvaluationNullUnit.newUnit Y).trans (InputSeedEvaluationNull.newNull Y true))
    (GlobalRawBass.InputIdentitySeedNull.oldNull g false).symm
    ((GlobalRawBass.InputIdentitySeedConjugation.oldUnit g).trans
      (GlobalRawBass.InputIdentitySeedNull.oldNull g true))
    (fun t => newNull g false (unitInterval.symm t))
    (two_maps_trans (InputSeedPostMap.map g) (InputSeedRawMap.map g)
      (InputSeedEvaluationNullUnit.newUnit Y) (InputSeedEvaluationNull.newNull Y true)
      (GlobalRawBass.InputIdentitySeedConjugation.oldUnit g)
      (GlobalRawBass.InputIdentitySeedNull.oldNull g true) (newUnit g) (newNull g true)) s

/-- The two prescribed long-route faces meet on their entire original intermediate seed word. -/
theorem face (s : I) : InputSeedPostFace.parameter g (1, s) =
    InputSeedTransitionFace.parameter g (0, s) :=
  (InputSeedPostFace.target g s).trans
    ((word g s).trans (InputSeedTransitionFace.source g s).symm)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedPostTargetSeam
