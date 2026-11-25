/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputDescNative
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartReference
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceWhiskering
public import Colib.KTheory.Waldhausen.Iterated.SimplexWhiskering
public import Colib.KTheory.Waldhausen.Iterated.SimplexCollapsedEdges

/-!
# Evaluation of the raw Bass descent square

The raw two-chart descent square is evaluated by precomposing its native simplex with
the bounded-flat global-section evaluation. Both geometric clocks are retained.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputRawDesc

open GlobalSectionChangeIndex

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The entire original raw descent simplex after the actual global-section evaluation. -/
def simplex :=
  (GlobalRawBass.InputDescSimplex.simplex g).precomp (evaluationModel (op Y))

/-- The common strict reference for the two evaluated chart faces. -/
abbrev sourceMap :=
  InputMixedDesc.sourceMap g

/-- A native chart node with a chosen reference from strict global evaluation. -/
abbrev Node :=
  Σ F : boundedAboveFlatGlobalSectionModelFunctor.obj (op Y) ⟶
      asSmallCategory (boundedAboveFlatPerfectWaldhausen (laurent.obj X).toRingedSpace),
    (sourceMap g).hom.toFunctor ≅ F.hom.toFunctor

set_option maxHeartbeats 1000000 in
-- The original anchor has the same target after reducing the two concrete Model maps.
/-- Precomposition retains the entire raw node and its actual evaluation anchor. -/
def evaluateNode (N : GlobalRawBass.InputDescSimplex.Node g) : Node g :=
  ⟨evaluationModel (op Y) ≫ N.1,
    evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y) ≪≫
      isoWhiskerLeft (evaluationModel (op Y)).hom.toFunctor N.2⟩

/-- All 31 raw nodes retain both the actual functor and the evaluated comparison anchor. -/
def nodes (i : Fin 31) : Node g :=
  evaluateNode g (GlobalRawBass.InputDescSimplex.nodes g i)

/-- The complete positive chart uses unchanged evaluated raw nodes. -/
theorem plus_nodes (i : Fin 18) :
    nodes g (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom i) =
      evaluateNode g
        (GlobalRawBass.InputDescSimplex.chartNodes g plus GlobalRawBass.plus_projection i) :=
  congrArg (evaluateNode g) (GlobalRawBass.InputDescSimplex.plus_nodes g i)

/-- The complete inverse chart uses unchanged evaluated raw nodes, including the five anchors. -/
theorem minus_nodes (i : Fin 18) :
    nodes g (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom i) =
      evaluateNode g
        (GlobalRawBass.InputDescSimplex.chartNodes g minus GlobalRawBass.minus_projection i) :=
  congrArg (evaluateNode g) (GlobalRawBass.InputDescSimplex.minus_nodes g i)

set_option maxHeartbeats 1000000 in
-- The generic precomposition and reanchoring laws are checked against the concrete section maps.
/-- The shared mixed reference simplex is exactly the original precomposed raw simplex. -/
theorem simplex_eq_ofIsos :
    simplex g = ModelSimplex.ofIsos (sourceMap g) (fun i => (nodes g i).1)
      (fun i => (nodes g i).2) := by
  let ref := GlobalRawBass.InputDescSimplex.reference g
  let maps := fun i => (GlobalRawBass.InputDescSimplex.nodes g i).1
  let anchors := fun i => (GlobalRawBass.InputDescSimplex.nodes g i).2
  have pre := ModelSimplex.ofIsos_precomp ref maps anchors (evaluationModel (op Y))
  have changeRef := ModelSimplex.ofIsos_change_reference
    (F₀ := sourceMap g) (F₁ := evaluationModel (op Y) ≫ ref)
    (evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y))
    (fun i => evaluationModel (op Y) ≫ maps i)
    (fun i => isoWhiskerLeft (evaluationModel (op Y)).hom.toFunctor (anchors i))
  exact pre.trans changeRef.symm

/-- Evaluating the mixed raw face retains the whole original two-chart quotient-collapse square. -/
theorem square_native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    prespectrumSimplexFamily (simplex g) n
      (BoundedFlatCoefficientBassH0Diagram.parameter (r, s), x) =
      (GlobalRawBass.inputDescPasting g).toSquare.level n
        (r, (s, (prespectrumMap (evaluationModel (op Y))).map n x)) :=
  (prespectrumSimplexFamily_precomp (GlobalRawBass.InputDescSimplex.simplex g)
    (evaluationModel (op Y)) n (BoundedFlatCoefficientBassH0Diagram.parameter (r, s)) x).trans
      (GlobalRawBass.InputDescSimplex.square_native g n r s
        ((prespectrumMap (evaluationModel (op Y))).map n x))

/-- The same native face evaluates the complete cylinder of the selected raw comparison. -/
theorem cylinder_native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    prespectrumSimplexFamily (simplex g) n
      (BoundedFlatCoefficientBassH0Diagram.parameter (r, s), x) =
      (GlobalRawBass.inputComparisonHomotopy g).level n
        (r, HomotopyPushout.cylinder
          (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y)) n
          (s, (prespectrumMap (evaluationModel (op Y))).map n x)) :=
  (prespectrumSimplexFamily_precomp (GlobalRawBass.InputDescSimplex.simplex g)
    (evaluationModel (op Y)) n (BoundedFlatCoefficientBassH0Diagram.parameter (r, s)) x).trans
      (GlobalRawBass.InputDescSimplex.cylinder_native g n r s
        ((prespectrumMap (evaluationModel (op Y))).map n x))

/-- The complete raw square parameter in the same compact mixed nerve as both moving faces. -/
def parameter :=
  (CommonReferenceNerve.parameter (sourceMap g) (nodes g)).comp
    BoundedFlatCoefficientBassH0Diagram.parameter

/-- The raw compact parameter retains every point of the original selected quotient surface. -/
theorem parameter_native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (sourceMap g) (parameter g) n ((r, s), x) =
      (GlobalRawBass.inputDescPasting g).toSquare.level n
        (r, (s, (prespectrumMap (evaluationModel (op Y))).map n x)) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ (parameter g)
    (nodes g) (r, s) (BoundedFlatCoefficientBassH0Diagram.parameter (r, s)) rfl n x).trans ?_
  rw [← simplex_eq_ofIsos g]
  exact square_native g n r s x

/-- Positive face restriction in the mixed nerve, with every selected vertex unchanged. -/
theorem plus_characteristic (z : StdSimplex ℝ (Fin 18)) :
    CommonReferenceNerve.parameter (sourceMap g) (nodes g)
      (StdSimplex.map BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom z) =
    CommonReferenceNerve.parameter (sourceMap g)
      (fun i => evaluateNode g
        (GlobalRawBass.InputDescSimplex.chartNodes g plus GlobalRawBass.plus_projection i)) z :=
  (CommonReferenceNerve.parameter_face (sourceMap g) (nodes g)
    BoundedFlatCoefficientBassH0Diagram.plusFace z).trans
    (congrArg (fun ns => CommonReferenceNerve.parameter (sourceMap g) ns z)
      (funext (plus_nodes g)))

/-- Inverse face restriction in the same mixed nerve, retaining the original common anchors. -/
theorem minus_characteristic (z : StdSimplex ℝ (Fin 18)) :
    CommonReferenceNerve.parameter (sourceMap g) (nodes g)
      (StdSimplex.map BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom z) =
    CommonReferenceNerve.parameter (sourceMap g)
      (fun i => evaluateNode g
        (GlobalRawBass.InputDescSimplex.chartNodes g minus GlobalRawBass.minus_projection i)) z :=
  (CommonReferenceNerve.parameter_face (sourceMap g) (nodes g)
    BoundedFlatCoefficientBassH0Diagram.minusFace z).trans
    (congrArg (fun ns => CommonReferenceNerve.parameter (sourceMap g) ns z)
      (funext (minus_nodes g)))

open CategoryTheory.Waldhausen.IteratedS.SimplexParameters in
/-- The left edge of the raw face uses the literal bottom-left quotient clock. -/
theorem parameter_left (r : unitInterval) :
    parameter g (r, 0) = CommonReferenceNerve.parameter (sourceMap g) (nodes g)
      (BoundedFlatCoefficientBassH0Diagram.boundaryParameter (1, ThreeSideSquare.leftTime r)) := by
  unfold parameter BoundedFlatCoefficientBassH0Diagram.parameter
  change CommonReferenceNerve.parameter (sourceMap g) (nodes g) (collapsed _ (r, 0)) = _
  rw [← ThreeSideSquare.collapse_leftTime r, collapsed_collapse]

open CategoryTheory.Waldhausen.IteratedS.SimplexParameters in
/-- The right edge retains the original right quotient clock. -/
theorem parameter_right (r : unitInterval) :
    parameter g (r, 1) = CommonReferenceNerve.parameter (sourceMap g) (nodes g)
      (BoundedFlatCoefficientBassH0Diagram.boundaryParameter (1, ThreeSideSquare.rightTime r)) := by
  unfold parameter BoundedFlatCoefficientBassH0Diagram.parameter
  change CommonReferenceNerve.parameter (sourceMap g) (nodes g) (collapsed _ (r, 1)) = _
  rw [← ThreeSideSquare.collapse_rightTime r, collapsed_collapse]

open CategoryTheory.Waldhausen.IteratedS.SimplexParameters in
/-- The source edge retains the literal source of the original projected paste. -/
theorem parameter_zero (s : unitInterval) :
    parameter g (0, s) = CommonReferenceNerve.parameter (sourceMap g) (nodes g)
      (BoundedFlatCoefficientBassH0Diagram.boundaryParameter (0, s)) := by
  unfold parameter BoundedFlatCoefficientBassH0Diagram.parameter
  change CommonReferenceNerve.parameter (sourceMap g) (nodes g) (collapsed _ (0, s)) = _
  exact congrArg (CommonReferenceNerve.parameter (sourceMap g) (nodes g))
    ((congrArg (collapsed _) (ThreeSideSquare.collapse_zero s)).symm.trans
      (collapsed_collapse _ (0, s)))

open CategoryTheory.Waldhausen.IteratedS.SimplexParameters in
/-- The target edge retains the original nested path, evaluated at the exact top quotient clock. -/
theorem parameter_one (s : unitInterval) :
    parameter g (1, s) = CommonReferenceNerve.parameter (sourceMap g) (nodes g)
      (BoundedFlatCoefficientBassH0Diagram.boundaryParameter (1, ThreeSideSquare.topTime s)) := by
  unfold parameter BoundedFlatCoefficientBassH0Diagram.parameter
  change CommonReferenceNerve.parameter (sourceMap g) (nodes g) (collapsed _ (1, s)) = _
  rw [← ThreeSideSquare.collapse_topTime s, collapsed_collapse]

open BoundedFlatPerfectProjectionRectangleParameters
open BoundedFlatCoefficientBassH0Diagram (plusFace minusFace)
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters

/-- Exact target-time extraction for the present native projection word, with its nested clocks. -/
theorem parameter_one_word (s : unitInterval) :
    parameter g (1, s) = CommonReferenceNerve.parameter (sourceMap g) (nodes g)
      (((Ppath plusFace).trans
        (((K plusFace).symm.trans (K minusFace)).trans (Ppath minusFace).symm)) s) :=
  congrArg (CommonReferenceNerve.parameter (sourceMap g) (nodes g))
    (collapsed_top_path BoundedFlatCoefficientBassH0Diagram.boundaryParameter s)

/-- The complete raw source clock is the specified two-chart composite path. -/
theorem parameter_zero_word (s : unitInterval) :
    parameter g (0, s) = CommonReferenceNerve.parameter (sourceMap g) (nodes g)
      (((D plusFace).symm.trans (D minusFace)) s) :=
  congrArg (CommonReferenceNerve.parameter (sourceMap g) (nodes g))
    (collapsed_zero_path BoundedFlatCoefficientBassH0Diagram.boundaryParameter s)

private def evaluateProjectionNode {A C D : Scheme.{u}} (c : D ⟶ C) (r : C ⟶ A)
    (N : BoundedFlatPerfectProjectionReference.Node c r) :
    Σ F : boundedAboveFlatGlobalSectionModelFunctor.obj (op A) ⟶ asSmallCategory
        (boundedAboveFlatPerfectWaldhausen D.toRingedSpace),
      (boundedAboveFlatGlobalSectionModelFunctor.map (c ≫ r).op ≫
        evaluationModel (op D)).hom.toFunctor ≅ F.hom.toFunctor :=
  ⟨evaluationModel (op A) ≫ N.1,
    evaluationComparisonIso (c ≫ r) ≪≫
      isoWhiskerLeft (evaluationModel (op A)).hom.toFunctor N.2⟩

private def evaluateTripleNode {A B C D : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (c : D ⟶ C)
    (N : BoundedFlatPerfectDoubleSquareCommonSimplex.Node p q c) : InputTripleNodes.Node c q p :=
  ⟨evaluationModel (op A) ≫ N.1,
    evaluationComparisonIso (c ≫ q ≫ p) ≪≫
      isoWhiskerLeft (evaluationModel (op A)).hom.toFunctor N.2⟩

private theorem reanchor_refl_family {U V : WideSubcategory
      SmallWaldhausenCategory.preservesZero.{u}} {F : U ⟶ V} {n : ℕ}
    (N : Fin (n + 1) → Σ G : U ⟶ V, F.hom.toFunctor ≅ G.hom.toFunctor) :
    ModelSimplex.reanchorNodes (F₀ := F) (F₁ := F) (Iso.refl F.hom.toFunctor) N = N := by
  funext i
  dsimp only [ModelSimplex.reanchorNodes, ModelSimplex.reanchorNode]
  rw [Iso.refl_trans]

set_option maxHeartbeats 1200000 in
-- Normalize the abstract projection before specializing either Laurent chart, as in
-- Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalRawBassInputDescNodes.lean.
-- Source revision: c561118b7795eb9780be9ed391c3251d6a4d0afd.
private theorem evaluate_reference_family {A B C D : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (c : D ⟶ C) (r : C ⟶ A) (hr : q ≫ p = r)
    {n : ℕ} (N : Fin (n + 1) → BoundedFlatPerfectDoubleSquareCommonSimplex.Node p q c) :
    ModelSimplex.reanchorNodes
      (F₀ := boundedAboveFlatGlobalSectionModelFunctor.map (c ≫ r).op ≫ evaluationModel (op D))
      (F₁ := InputTripleNodes.sourceMap c q p)
      (eqToIso (congrArg (fun j : D ⟶ A =>
        (boundedAboveFlatGlobalSectionModelFunctor.map j.op ≫
          evaluationModel (op D)).hom.toFunctor)
        (congrArg (fun j => c ≫ j) hr).symm))
      (fun i => evaluateTripleNode p q c (N i)) =
    fun i => evaluateProjectionNode c r
      (ModelSimplex.reanchorNodes
        (F₀ := BoundedFlatPerfectProjectionReference.reference c r)
        (F₁ := BoundedFlatPerfectTripleSimplex.source c q p)
        (eqToIso (BoundedFlatPerfectProjectionReference.anchor p q c r hr)) N i) := by
  subst r
  let S := InputTripleNodes.sourceMap c q p
  let R := BoundedFlatPerfectTripleSimplex.source c q p
  change ModelSimplex.reanchorNodes (F₀ := S) (F₁ := S) (Iso.refl S.hom.toFunctor)
      (fun i => evaluateTripleNode p q c (N i)) =
    fun i => evaluateProjectionNode c (q ≫ p)
      (ModelSimplex.reanchorNodes (F₀ := R) (F₁ := R) (Iso.refl R.hom.toFunctor) N i)
  rw [reanchor_refl_family]
  exact (congrArg
    (fun M : Fin (n + 1) → BoundedFlatPerfectDoubleSquareCommonSimplex.Node p q c =>
      fun i => evaluateProjectionNode c (q ≫ p) (M i))
    (reanchor_refl_family (F := BoundedFlatPerfectTripleSimplex.source c q p) N)).symm

private theorem raw_rectangle_evaluated {A B C A' B' C' : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
    (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
    (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b) :
    InputRectangleNodes.rawNode p q p' q' a b c hp hq =
      fun i => evaluateTripleNode p q c
        (BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq i) := rfl

private theorem projection_nodes_reanchored {A B C A' B' C' : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
    (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
    (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
    (r : C ⟶ A) (hr : q ≫ p = r) :
    BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr =
      ModelSimplex.reanchorNodes
        (F₀ := BoundedFlatPerfectProjectionReference.reference c r)
        (F₁ := BoundedFlatPerfectTripleSimplex.source c q p)
        (eqToIso (BoundedFlatPerfectProjectionReference.anchor p q c r hr))
        (BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq) := rfl

private theorem raw_rectangle_family {A B C A' B' C' : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
    (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
    (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
    (r : C ⟶ A) (hr : q ≫ p = r) :
    ModelSimplex.reanchorNodes
      (F₀ := boundedAboveFlatGlobalSectionModelFunctor.map (c ≫ r).op ≫ evaluationModel (op C'))
      (F₁ := InputTripleNodes.sourceMap c q p)
      (eqToIso (congrArg (fun j : C' ⟶ A =>
        (boundedAboveFlatGlobalSectionModelFunctor.map j.op ≫
          evaluationModel (op C')).hom.toFunctor)
        (congrArg (fun j => c ≫ j) hr).symm))
      (InputRectangleNodes.rawNode p q p' q' a b c hp hq) =
    fun i => evaluateProjectionNode c r
      (BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr i) := by
  rw [raw_rectangle_evaluated, projection_nodes_reanchored]
  exact evaluate_reference_family p q c r hr
    (BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq)

private theorem chart_node_family (k : laurent ⟶ polynomial)
    (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z) :
    InputChartReference.rawNode g k hk =
      fun i => evaluateNode g (GlobalRawBass.InputDescSimplex.chartNodes g k hk i) :=
  raw_rectangle_family (projection.app Y) (k.app Y) (projection.app X) (k.app X)
    g (polynomial.map g) (laurent.map g) (projection.naturality g) (k.naturality g)
    (GlobalRawBass.laurentProjection.app Y) (hk Y)

/-- Each chart restriction agrees as a full Model arrow and chosen Laurent anchor. -/
theorem chart_node (k : laurent ⟶ polynomial)
    (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)
    (i : Fin 18) :
    InputChartReference.rawNode g k hk i =
      evaluateNode g (GlobalRawBass.InputDescSimplex.chartNodes g k hk i) :=
  congrFun (chart_node_family g k hk) i

/-- The positive raw characteristic face uses the identical full mixed chart nodes. -/
theorem plus_chart_characteristic (z : StdSimplex ℝ (Fin 18)) :
    CommonReferenceNerve.parameter (sourceMap g) (nodes g)
      (StdSimplex.map plusFace.toOrderHom z) =
    CommonReferenceNerve.parameter (sourceMap g)
      (InputChartReference.rawNode g plus GlobalRawBass.plus_projection) z :=
  (plus_characteristic g z).trans
    (congrArg (fun ns => CommonReferenceNerve.parameter (sourceMap g) ns z)
      (funext (chart_node g plus GlobalRawBass.plus_projection))).symm

/-- The inverse raw characteristic face uses the identical full mixed chart nodes. -/
theorem minus_chart_characteristic (z : StdSimplex ℝ (Fin 18)) :
    CommonReferenceNerve.parameter (sourceMap g) (nodes g)
      (StdSimplex.map minusFace.toOrderHom z) =
    CommonReferenceNerve.parameter (sourceMap g)
      (InputChartReference.rawNode g minus GlobalRawBass.minus_projection) z :=
  (minus_characteristic g z).trans
    (congrArg (fun ns => CommonReferenceNerve.parameter (sourceMap g) ns z)
      (funext (chart_node g minus GlobalRawBass.minus_projection))).symm

open BoundedFlatPerfectDoubleSquareScalarPaths

/-- The left face retains the exact two signed positive polynomial-square paths. -/
theorem plus_left_chart (r : unitInterval) :
    parameter g (r, 0) = CommonReferenceNerve.parameter (sourceMap g)
      (InputChartReference.rawNode g plus GlobalRawBass.plus_projection)
      ((firstRestriction.symm.trans secondRestriction) r) := by
  have h := plus_chart_characteristic g ((firstRestriction.symm.trans secondRestriction) r)
  have hmap : embed plusFace ((firstRestriction.symm.trans secondRestriction) r) =
      L plusFace r :=
    map_trans_values (embed plusFace) firstRestriction.symm secondRestriction
      (binaryPath (plusFace.toOrderHom 9) (plusFace.toOrderHom 10) (plusFace.toOrderHom 11)).symm
      (binaryPath (plusFace.toOrderHom 9) (plusFace.toOrderHom 12) (plusFace.toOrderHom 13))
      (fun t => map_binaryPath plusFace 9 10 11 (unitInterval.symm t))
      (map_binaryPath plusFace 9 12 13) r
  change CommonReferenceNerve.parameter (sourceMap g) (nodes g)
    (embed plusFace ((firstRestriction.symm.trans secondRestriction) r)) = _ at h
  rw [hmap] at h
  exact (congrArg (CommonReferenceNerve.parameter (sourceMap g) (nodes g))
    (collapsed_left_path BoundedFlatCoefficientBassH0Diagram.boundaryParameter r)).trans h

/-- The right face retains the exact inverse polynomial-square paths and chosen anchor. -/
theorem minus_right_chart (r : unitInterval) :
    parameter g (r, 1) = CommonReferenceNerve.parameter (sourceMap g)
      (InputChartReference.rawNode g minus GlobalRawBass.minus_projection)
      ((firstRestriction.symm.trans secondRestriction) r) := by
  have h := minus_chart_characteristic g ((firstRestriction.symm.trans secondRestriction) r)
  have hmap : embed minusFace ((firstRestriction.symm.trans secondRestriction) r) =
      L minusFace r :=
    map_trans_values (embed minusFace) firstRestriction.symm secondRestriction
      (binaryPath (minusFace.toOrderHom 9) (minusFace.toOrderHom 10) (minusFace.toOrderHom 11)).symm
      (binaryPath (minusFace.toOrderHom 9) (minusFace.toOrderHom 12) (minusFace.toOrderHom 13))
      (fun t => map_binaryPath minusFace 9 10 11 (unitInterval.symm t))
      (map_binaryPath minusFace 9 12 13) r
  change CommonReferenceNerve.parameter (sourceMap g) (nodes g)
    (embed minusFace ((firstRestriction.symm.trans secondRestriction) r)) = _ at h
  rw [hmap] at h
  exact (congrArg (CommonReferenceNerve.parameter (sourceMap g) (nodes g))
    (collapsed_right_path BoundedFlatCoefficientBassH0Diagram.boundaryParameter r)).trans h

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputRawDesc
