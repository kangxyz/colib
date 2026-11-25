/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedUnitNodes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumBinaryPath
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCubeExtension

/-! The original split binary normalization path at an independently moving evaluation input. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite Convexity Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvalBinary
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedCarrier
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

private theorem terminal_value {A B T : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace T]
    (F : C(T, B)) (J : C(I × A, B)) (K : C(A, B))
    (q : C(T, I × A)) (h : F = J.comp q)
    (hJ : ∀ y, J (1, y) = K y) (t : T) (y : A) (hq : q t = (1, y)) :
    F t = K y := by
  rw [h, ContinuousMap.comp_apply, hq]
  exact hJ y

private theorem comparison_terminal {E F : LoopPrespectrum.{u}}
    {f g : E ⟶ F} {H K : Homotopy f g} (J : H.RelHomotopy K)
    (n : ℕ) (z : I × E.space n) :
    (J.level n).toContinuousMap (1, z) = K.level n z :=
  (J.level n).apply_one z

/-- The original binary path retains its two halves at every independent evaluation time. -/
def scalar : C(I × I, StdSimplex ℝ (Fin 6)) :=
  ⟨fun z ↦ Topology.SimplexGrid.parameter.{u} 1 2
    ((edge (k := 1) 0 1) z.1, binaryPath (k := 2) 0 1 2 z.2), by fun_prop⟩

/-- The raw split path is the terminal face of the existing comparison triangle. -/
theorem scalar_terminal (r s : I) :
    scalar.{u} (r, s) = InputNormalizationPrism.parameter.{u} (r, (1, s)) := by
  change Topology.SimplexGrid.parameter 1 2
    ((edge (k := 1) 0 1) r, binaryPath (k := 2) 0 1 2 s) =
      Topology.SimplexGrid.parameter 1 2
        ((edge (k := 1) 0 1) r, CategoryTheory.TheoremB.compositionTriangleHomotopy (1, s))
  rw [CategoryTheory.TheoremB.compositionTriangleHomotopy.apply_one]
  rfl

/-- The entire binary surface stays in the actual shared Laurent-reference nerve. -/
def parameter : C(I × I, |nerve (Codiscrete (Node (laurentRef g)))|) :=
  (CommonReferenceNerve.parameter (laurentRef g)
    (InputChartReference.prismNode g plus GlobalRawBass.plus_projection)).comp scalar.{u+1}

/-- Its exact original prism parameter is retained at every evaluation and binary time. -/
theorem parameter_terminal (r s : I) : parameter g (r, s) =
    InputChartReference.prismParameter g plus GlobalRawBass.plus_projection (r, (1, s)) :=
  congrArg (CommonReferenceNerve.parameter (laurentRef g)
    (InputChartReference.prismNode g plus GlobalRawBass.plus_projection)) (scalar_terminal r s)

/-- The full native surface is the original positive split composition at the moving input. -/
theorem native (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    compactPrespectrumFamily (laurentRef g) (parameter g) n ((r, s), x) =
      (GlobalRawBass.plusHomotopy X).level n (s, (evaluationComparison g).level n (r, x)) := by
  rw [GlobalRawBass.plusHomotopy, Homotopy.cast_level]
  refine (compactFamily_of_point_eq (laurentRef g) (parameter g)
    (InputChartReference.prismParameter g plus GlobalRawBass.plus_projection)
    (r, s) (r, (1, s)) (parameter_terminal g r s) n x).trans ?_
  exact terminal_value
    (compactPrespectrumFamily (laurentRef g)
      (InputChartReference.prismParameter g plus GlobalRawBass.plus_projection) n)
    ((boundedAboveFlatPerfectNormalizedCompTrackComparison
      (plus.app X) (projection.app X)).level n).toContinuousMap
    ((boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy
      (plus.app X) (projection.app X)).level n)
    (InputNormalizationPrism.movingParameter g n)
    (InputChartReference.prism_whole_native g plus GlobalRawBass.plus_projection n)
    (comparison_terminal
      (boundedAboveFlatPerfectNormalizedCompTrackComparison (plus.app X) (projection.app X)) n)
    ((r, (1, s)), x) (s, (evaluationComparison g).level n (r, x)) rfl

/-- The final polynomial node travels along the actual projection-evaluation edge. -/
def polynomialParameter : C(I, |nerve (Codiscrete (Node (polyRef g)))|) :=
  (CommonReferenceNerve.parameter (polyRef g) (InputSpanParameterNodes.projectionNodes g)).comp
    (edge (k := 7) 6 7).toContinuousMap

private def terminalFace : ⦋1⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![6, 7], by decide⟩

/-- The whole binary target is exactly the prescribed ordinary polynomial attachment. -/
theorem target_attachment (r : I) : parameter g (r, 1) =
    mapParameter (attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g) (ordinary g))
      (polynomialParameter g r) := by
  change CommonReferenceNerve.parameter (laurentRef g)
    (InputChartReference.prismNode g plus GlobalRawBass.plus_projection)
    (Topology.SimplexGrid.parameter.{u+1} 1 2
      ((edge (k := 1) 0 1) r, binaryPath (k := 2) 0 1 2 1)) = _
  rw [Path.target, Topology.SimplexGrid.parameter_column]
  have h := parameter_eq_of_face_nodes (laurentRef g)
    (InputSpanParameterNodes.nodes g plus GlobalRawBass.plus_projection)
    (InputChartReference.prismNode g plus GlobalRawBass.plus_projection)
    terminalFace (Topology.SimplexGrid.columnFace 1 2 2)
    (fun i ↦ by
      fin_cases i
      · exact (InputSpanParameterNodes.node_six g plus GlobalRawBass.plus_projection).symm
      · exact (InputSpanParameterNodes.node_seven g plus GlobalRawBass.plus_projection).symm)
    ((edge (k := 1) 0 1) r)
  have he : StdSimplex.map terminalFace.toOrderHom ((edge (k := 1) 0 1) r) =
      (edge (k := 7) 6 7) r := map_edge terminalFace 0 1 r
  refine h.trans ((congrArg
    (CommonReferenceNerve.parameter (laurentRef g)
      (InputSpanParameterNodes.nodes g plus GlobalRawBass.plus_projection)) he).trans ?_)
  change _ = mapParameter _ (CommonReferenceNerve.parameter (polyRef g)
    (InputSpanParameterNodes.projectionNodes g) ((edge (k := 7) 6 7) r))
  rw [mapParameter_parameter]
  rfl

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvalBinary
