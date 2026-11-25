/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputNormalizationPrismNative
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSquareFivePath

/-!
# The actual raw square at a moving evaluation input

The original two-node evaluation comparison and five-node raw geometric square form their
literal categorical product. Its complete native family retains the two independent times,
including the original reverse-forward square clock and the independent level-zero loop.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters Topology AlgebraicGeometry.RingedSpace
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputRawSquareProduct
open GlobalSectionChangeIndex InputNormalizationPrism
variable {X Y Z T U : Scheme.{u}}
  (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z)
  (h : p ≫ v = q ≫ w) (a : Z ⟶ U)

/-- Every original square vertex keeps its genuine polynomial-source Model arrow. -/
def squareVertices := fun i : Fin 5 =>
  (BoundedFlatPerfectNativeSquareFiveSimplex.nodes p v q w h i).1

/-- Both original binary normalization references retain the actual commuting-square transport. -/
def squareAnchors := fun i : Fin 5 =>
  (BoundedFlatPerfectNativeSquareFiveSimplex.nodes p v q w h i).2

/-- The original square factor is retained as an entire Model simplex. -/
theorem square_simplex :
    ModelSimplex.ofIsos (BoundedFlatPerfectNativeSquareFiveSimplex.source p v)
      (squareVertices p v q w h) (squareAnchors p v q w h) =
    BoundedFlatPerfectNativeSquareFiveSimplex.simplex p v q w h := rfl

/-- Ten actual composite vertices retain the original independent evaluation and square factors. -/
def simplex :=
  CommonReferenceProduct.simplex (firstSource a) (firstVertices a) (firstAnchors a)
    (BoundedFlatPerfectNativeSquareFiveSimplex.source p v)
    (squareVertices p v q w h) (squareAnchors p v q w h)

/-- The full product parameter keeps the original evaluation and square times independent. -/
def parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 10)) :=
  ⟨fun z => SimplexGrid.parameter.{u} 1 4
    ((edge (k := 1) 0 1) z.1, BoundedFlatPerfectNativeSquareFiveSimplex.parameter z.2),
    by fun_prop⟩

/-- The original evaluation-source row retains the entire raw square path. -/
theorem parameter_evaluation_zero (s : unitInterval) :
    parameter.{u} (0, s) =
      StdSimplex.map (SimplexGrid.rowFace 1 4 0).toOrderHom
        (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) := by
  change SimplexGrid.parameter 1 4
    ((edge (k := 1) 0 1) 0, BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) = _
  rw [Path.source]
  exact SimplexGrid.parameter_row 1 4 0 _

/-- The evaluated target row retains the same original raw square path without reparametrization. -/
theorem parameter_evaluation_one (s : unitInterval) :
    parameter.{u} (1, s) =
      StdSimplex.map (SimplexGrid.rowFace 1 4 1).toOrderHom
        (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) := by
  change SimplexGrid.parameter 1 4
    ((edge (k := 1) 0 1) 1, BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) = _
  rw [Path.target]
  exact SimplexGrid.parameter_row 1 4 1 _

/-- The source of the reverse-forward square keeps the complete actual evaluation edge. -/
theorem parameter_square_zero (t : unitInterval) :
    parameter.{u} (t, 0) =
      StdSimplex.map (SimplexGrid.columnFace 1 4 2).toOrderHom
        ((edge (k := 1) 0 1) t) := by
  change SimplexGrid.parameter 1 4
    ((edge (k := 1) 0 1) t, BoundedFlatPerfectNativeSquareFiveSimplex.parameter 0) = _
  rw [Path.source]
  exact SimplexGrid.parameter_column 1 4 2 _

/-- The square's target keeps the distinct original raw suffix throughout evaluation. -/
theorem parameter_square_one (t : unitInterval) :
    parameter.{u} (t, 1) =
      StdSimplex.map (SimplexGrid.columnFace 1 4 4).toOrderHom
        ((edge (k := 1) 0 1) t) := by
  change SimplexGrid.parameter 1 4
    ((edge (k := 1) 0 1) t, BoundedFlatPerfectNativeSquareFiveSimplex.parameter 1) = _
  rw [Path.target]
  exact SimplexGrid.parameter_column 1 4 4 _

private def squareFamily (n : ℕ) :=
  (prespectrumSimplexFamily (BoundedFlatPerfectNativeSquareFiveSimplex.simplex p v q w h) n).comp
    (⟨fun z => (BoundedFlatPerfectNativeSquareFiveSimplex.parameter z.1, z.2), by fun_prop⟩ :
      C(unitInterval × (prespectrum
        (asSmallCategory (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace))).space n, _))

private theorem square_whole (n : ℕ) :
    squareFamily p v q w h n =
      (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy p v q w h).level n := by
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  exact BoundedFlatPerfectNativeSquareFiveSimplex.native p v q w h n s x

/-- The original square time and moving evaluation input retain their separate coordinates. -/
def movingParameter (n : ℕ) :
    C((unitInterval × unitInterval) ×
        (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op U))).space n,
      unitInterval × (prespectrum
        (asSmallCategory (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace))).space n) :=
  ⟨fun z => (z.1.2, (evaluationComparison a).level n (z.1.1, z.2)), by fun_prop⟩

/-- The original ten-node product is evaluated as one jointly continuous two-time family. -/
def nativeFamily (n : ℕ) :=
  (prespectrumSimplexFamily (simplex p v q w h a) n).comp
    (⟨fun z => (parameter.{u+1} z.1, z.2), by fun_prop⟩ :
      C((unitInterval × unitInterval) ×
        (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op U))).space n, _))

private theorem model_whole (n : ℕ) :
    nativeFamily p v q w h a n = (squareFamily p v q w h n).comp (movingParameter a n) := by
  apply ContinuousMap.ext
  rintro ⟨⟨t, s⟩, x⟩
  change prespectrumSimplexFamily (simplex p v q w h a) n
    (parameter.{u+1} (t, s), x) =
      prespectrumSimplexFamily (BoundedFlatPerfectNativeSquareFiveSimplex.simplex p v q w h) n
        (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s,
          (evaluationComparison a).level n (t, x))
  exact (CommonReferenceProduct.prespectrum_comp
    (firstSource a) (firstVertices a) (firstAnchors a)
    (BoundedFlatPerfectNativeSquareFiveSimplex.source p v)
    (squareVertices p v q w h) (squareAnchors p v q w h)
    n x ((edge (k := 1) 0 1) t) (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s)).trans
    ((congrArg (fun S => prespectrumSimplexFamily S n
      (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s,
        prespectrumSimplexFamily (firstSimplex a) n ((edge (k := 1) 0 1) t, x)))
      (square_simplex p v q w h)).trans
      (congrArg (fun y => prespectrumSimplexFamily
        (BoundedFlatPerfectNativeSquareFiveSimplex.simplex p v q w h) n
        (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s, y))
        (first_native a n t x)))

/-- The whole original raw square acts on every point of the actual moving evaluation family. -/
theorem whole_native (n : ℕ) :
    nativeFamily p v q w h a n =
      ((boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy p v q w h).level n).comp
        (movingParameter a n) :=
  (model_whole p v q w h a n).trans
    (congrArg (fun F => F.comp (movingParameter a n)) (square_whole p v q w h n))

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputRawSquareProduct
