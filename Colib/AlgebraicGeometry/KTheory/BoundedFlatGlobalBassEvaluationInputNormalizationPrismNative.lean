/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputNormalizationPrism
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitTripleEvaluation
public import Colib.KTheory.Waldhausen.Iterated.RealizationSimplexComposition
public import Colib.KTheory.Waldhausen.Iterated.ScalarRouteExtraction
public import Colib.KTheory.Waldhausen.Iterated.SimplexPostwhiskering
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveParameter

/-!
# The original three-parameter evaluation-normalization prism

The actual product-realization parameter keeps the evaluation time independent of both
original normalization comparison times. Its full native family, both whole rows, and all
three original evaluation columns retain their specified clocks.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.RingedSpace Topology
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputNormalizationPrism
open GlobalSectionChangeIndex SmallWaldhausenCategory
variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- Repeating the terminal vertex extracts the unchanged first evaluation edge. -/
def firstTriangleFace : ⦋2⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 1, 1], by decide⟩

/-- The entire degenerate face uses the original evaluation transformation and identity. -/
theorem first_triangle_face : (firstSimplex h).face firstTriangleFace =
    ModelSimplex.triangle (F := firstSource h) (G := firstTarget h) (H := firstTarget h)
      (evaluationComparisonIso h).hom (𝟙 _)
      (fun _ ↦ (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace).asSmall.weq_iso _ inferInstance)
      (fun _ ↦
        (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace).asSmall.weq_iso _ inferInstance) := by
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact Category.comp_id _

private theorem first_triangle_native :
    HomotopyLift (firstSimplex h) (triangle firstTriangleFace)
      (prespectrumTransformationCompositionHomotopy
        (F := firstSource h) (G := firstTarget h) (H := firstTarget h)
        (evaluationComparisonIso h).hom (𝟙 _)
        (fun _ ↦
          (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace).asSmall.weq_iso _ inferInstance)
        (fun _ ↦
          (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace).asSmall.weq_iso _ inferInstance)) :=
  triangle_lift _ _ _ _ _ _ (first_triangle_face h)

/-- Every point of the first factor is the original evaluation comparison, with no new pause. -/
theorem first_native :
    PathLift (firstSimplex h) (edge (k := 1) 0 1) (evaluationComparison h) := by
  have he := PathLift.trans_left _ (HomotopyLift.target _ (first_triangle_native h))
  intro n t x
  exact he n t x

/-- The actual product parameter keeps all three times independent. -/
def parameter : C(unitInterval × (unitInterval × unitInterval), StdSimplex ℝ (Fin 6)) :=
  ⟨fun z ↦ SimplexGrid.parameter.{u} 1 2
    ((edge (k := 1) 0 1) z.1, TheoremB.compositionTriangleHomotopy z.2), by fun_prop⟩

/-- The initial evaluation face retains the entire original normalization parameter. -/
theorem parameter_evaluation_zero (r s : unitInterval) :
    parameter.{u} (0, (r, s)) =
      StdSimplex.map (SimplexGrid.rowFace 1 2 0).toOrderHom
        (TheoremB.compositionTriangleHomotopy (r, s)) := by
  change SimplexGrid.parameter 1 2
    ((edge (k := 1) 0 1) 0, TheoremB.compositionTriangleHomotopy (r, s)) = _
  rw [Path.source]
  exact SimplexGrid.parameter_row 1 2 0 _

/-- The terminal evaluation face retains the same whole normalization parameter. -/
theorem parameter_evaluation_one (r s : unitInterval) :
    parameter.{u} (1, (r, s)) =
      StdSimplex.map (SimplexGrid.rowFace 1 2 1).toOrderHom
        (TheoremB.compositionTriangleHomotopy (r, s)) := by
  change SimplexGrid.parameter 1 2
    ((edge (k := 1) 0 1) 1, TheoremB.compositionTriangleHomotopy (r, s)) = _
  rw [Path.target]
  exact SimplexGrid.parameter_row 1 2 1 _

/-- The direct normalization boundary keeps the independent evaluation time. -/
theorem parameter_normalization_zero (t s : unitInterval) :
    parameter.{u} (t, (0, s)) = SimplexGrid.parameter.{u} 1 2
      ((edge (k := 1) 0 1) t, TheoremB.triangleEdgePath 0 2 s) := by
  change SimplexGrid.parameter 1 2
    ((edge (k := 1) 0 1) t, TheoremB.compositionTriangleHomotopy (0, s)) = _
  rw [TheoremB.compositionTriangleHomotopy.apply_zero]
  rfl

/-- The split normalization boundary keeps the original two-half concatenation clock. -/
theorem parameter_normalization_one (t s : unitInterval) :
    parameter.{u} (t, (1, s)) = SimplexGrid.parameter.{u} 1 2
      ((edge (k := 1) 0 1) t,
        ((TheoremB.triangleEdgePath 0 1).trans
          (TheoremB.triangleEdgePath 1 2)) s) := by
  change SimplexGrid.parameter 1 2
    ((edge (k := 1) 0 1) t, TheoremB.compositionTriangleHomotopy (1, s)) = _
  rw [TheoremB.compositionTriangleHomotopy.apply_one]
  rfl

private def binaryFamily (n : ℕ) :
    C(unitInterval × (unitInterval ×
      (prespectrum (asSmallCategory (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace))).space n),
        (prespectrum (asSmallCategory
          (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))).space n) :=
  (prespectrumSimplexFamily (BoundedFlatPerfectBinarySimplex.simplex f g) n).comp
    ⟨fun z ↦ (TheoremB.compositionTriangleHomotopy (z.1, z.2.1), z.2.2),
      by fun_prop⟩

private theorem binary_model_whole (n : ℕ) :
    binaryFamily f g n =
      ((prespectrumTransformationCompositionHomotopy
        (BoundedFlatPerfectBinarySimplex.first f g).hom
          (BoundedFlatPerfectBinarySimplex.second f g).hom
        (fun _ ↦
          (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _
          inferInstance)).level n).toContinuousMap := by
  apply ContinuousMap.ext
  rintro ⟨r, s, x⟩
  exact BoundedFlatPerfectBinarySimplex.whole_triangle f g n r s x

private theorem binary_whole (n : ℕ) : binaryFamily f g n =
    ((boundedAboveFlatPerfectNormalizedCompTrackComparison f g).level n).toContinuousMap :=
  (binary_model_whole f g n).trans (by
    apply ContinuousMap.ext
    rintro ⟨r, s, x⟩
    exact (BoundedFlatPerfectBinarySimplex.native_apply f g n r s x).symm)

/-- The original moving evaluation input retains all three independent time coordinates. -/
def movingParameter (n : ℕ) :
    C((unitInterval × (unitInterval × unitInterval)) ×
      (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op T))).space n,
        unitInterval × (unitInterval ×
          (prespectrum (asSmallCategory
            (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace))).space n)) :=
  ⟨fun z ↦ (z.1.2.1, (z.1.2.2, (evaluationComparison h).level n (z.1.1, z.2))),
    by fun_prop⟩

/-- The entire native family over the actual product-realization parameter. -/
def nativeFamily (n : ℕ) :=
  (prespectrumSimplexFamily (simplex f g h) n).comp
    (⟨fun z ↦ (parameter.{u+1} z.1, z.2), by fun_prop⟩ :
      C((unitInterval × (unitInterval × unitInterval)) ×
        (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op T))).space n, _))

private theorem model_whole (n : ℕ) :
    nativeFamily f g h n = (binaryFamily f g n).comp (movingParameter h n) := by
  apply ContinuousMap.ext
  rintro ⟨⟨t, r, s⟩, x⟩
  exact (congrArg
    (fun S ↦ prespectrumSimplexFamily S n (parameter.{u+1} (t, (r, s)), x))
    (product_simplex f g h)).trans
      ((CommonReferenceProduct.prespectrum_comp (firstSource h) (firstVertices h) (firstAnchors h)
        (BoundedFlatPerfectBinarySimplex.sourceMap f g) (binaryVertices f g) (binaryAnchors f g)
        n x ((edge (k := 1) 0 1) t) (TheoremB.compositionTriangleHomotopy (r, s))).trans
        ((congrArg (fun S ↦ prespectrumSimplexFamily S n
          (TheoremB.compositionTriangleHomotopy (r, s),
            prespectrumSimplexFamily (firstSimplex h) n ((edge (k := 1) 0 1) t, x)))
          (binary_simplex f g)).trans
          (congrArg (fun y ↦ prespectrumSimplexFamily
            (BoundedFlatPerfectBinarySimplex.simplex f g) n
            (TheoremB.compositionTriangleHomotopy (r, s), y)) (first_native h n t x))))

/-- Equality of the complete continuous families precedes evaluation of the original raw track. -/
theorem whole_native (n : ℕ) :
    nativeFamily f g h n =
      ((boundedAboveFlatPerfectNormalizedCompTrackComparison f g).level n).toContinuousMap.comp
        (movingParameter h n) :=
  (model_whole f g h n).trans
    (congrArg (fun A ↦ A.comp (movingParameter h n)) (binary_whole f g n))

/-- Every point of the first row is the original unconverted normalization triangle. -/
theorem pre_row_parameter (z : StdSimplex ℝ (Fin 3)) :
    CommonReferenceNerve.parameter (InputTripleNodes.sourceMap f g h) (nodes f g h)
      (SimplexGrid.parameter.{u} 1 2 (StdSimplex.single 0, z)) =
    CommonReferenceNerve.parameter (InputTripleNodes.sourceMap f g h) (preNodes f g h) z := by
  refine (congrArg
    (CommonReferenceNerve.parameter (InputTripleNodes.sourceMap f g h) (nodes f g h))
    (SimplexGrid.parameter_row 1 2 _ z)).trans ?_
  refine (CommonReferenceNerve.parameter_face (InputTripleNodes.sourceMap f g h)
    (nodes f g h) (SimplexGrid.rowFace 1 2 _) z).trans ?_
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter (InputTripleNodes.sourceMap f g h) N z)
  funext i
  fin_cases i <;> rfl

/-- Every point of the second row retains the actual converted normalization references. -/
theorem converted_row_parameter (z : StdSimplex ℝ (Fin 3)) :
    CommonReferenceNerve.parameter (InputTripleNodes.sourceMap f g h) (nodes f g h)
      (SimplexGrid.parameter.{u} 1 2 (StdSimplex.single 1, z)) =
    CommonReferenceNerve.parameter (InputTripleNodes.sourceMap f g h) (convertedNodes f g h) z := by
  refine (congrArg
    (CommonReferenceNerve.parameter (InputTripleNodes.sourceMap f g h) (nodes f g h))
    (SimplexGrid.parameter_row 1 2 _ z)).trans ?_
  refine (CommonReferenceNerve.parameter_face (InputTripleNodes.sourceMap f g h)
    (nodes f g h) (SimplexGrid.rowFace 1 2 _) z).trans ?_
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter (InputTripleNodes.sourceMap f g h) N z)
  funext i
  fin_cases i <;> rfl

/-- The original three vertical families are the actual right-whiskered evaluation comparison. -/
theorem column_native (j : Fin 3) (n : ℕ) (t : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op T))).space n) :
    prespectrumSimplexFamily (simplex f g h) n
      (SimplexGrid.parameter.{u} 1 2 ((edge (k := 1) 0 1) t, StdSimplex.single j), x) =
    (prespectrumMap (binaryVertices f g j)).map n ((evaluationComparison h).level n (t, x)) := by
  exact (congrArg (fun z ↦ prespectrumSimplexFamily (simplex f g h) n (z, x))
    (SimplexGrid.parameter_column 1 2 j ((edge (k := 1) 0 1) t))).trans
    ((prespectrumSimplexFamily_face (simplex f g h)
      (SimplexGrid.columnFace 1 2 j) n ((edge (k := 1) 0 1) t) x).trans
      ((congrArg (fun S ↦ prespectrumSimplexFamily S n ((edge (k := 1) 0 1) t, x))
        (column_face f g h j)).trans
        ((prespectrumSimplexFamily_postcomp (firstSimplex h) (binaryVertices f g j)
          n ((edge (k := 1) 0 1) t) x).trans
          (congrArg ((prespectrumMap (binaryVertices f g j)).map n) (first_native h n t x)))))

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputNormalizationPrism
