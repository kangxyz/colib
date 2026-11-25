/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputRectangleNodes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareRectangleNative
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputNative
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceWhiskering
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCompactFamily
public import Colib.KTheory.Waldhausen.Iterated.SimplexPostwhiskering

/-!
# Whole original mixed rectangle and postcomposition faces

The two original full surfaces land in the same actual common-reference nerve. Their shared
normalization triangle is equal at every characteristic-map point, using the complete node
equalities. No cube boundary compatibility or mixed cone filling is inferred here.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputRectangleNodes
open GlobalSectionChangeIndex
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- The entire evaluated raw rectangle, with its complete original evaluation reference. -/
def rawSimplex := ModelSimplex.ofIsos (InputTripleNodes.sourceMap c q p)
  (fun i => (rawNode p q p' q' a b c hp hq i).1)
  (fun i => (rawNode p q p' q' a b c hp hq i).2)

/-- The original postcomposed evaluation chart with its complete first-comparison reference. -/
def postSimplex := ModelSimplex.ofIsos (InputTripleNodes.sourceMap c q p)
  (fun i => (InputTripleNodes.postNode c q p i).1)
  (fun i => (InputTripleNodes.postNode c q p i).2)

/-- Reanchoring leaves the entire original raw diagram after evaluation unchanged. -/
theorem raw_simplex : rawSimplex p q p' q' a b c hp hq =
    (BoundedFlatPerfectDoubleSquareMergedSimplex.simplex p q p' q' a b c hp hq).precomp
      (evaluationModel (op A)) := by
  unfold rawSimplex rawNode
  rw [ModelSimplex.ofIsos_change_reference]
  exact (ModelSimplex.ofIsos_precomp _ _ _ _).symm

/-- Reanchoring leaves the entire original evaluation diagram after raw pullback unchanged. -/
theorem post_simplex : postSimplex p q c =
    (InputSimplex.simplex q p).postcomp (evaluationRawMap c) := by
  unfold postSimplex InputTripleNodes.postNode
  rw [ModelSimplex.ofIsos_change_reference]
  exact (ModelSimplex.ofIsos_postcomp _ _ _ _).symm

/-- The actual normalization triangle in the original raw rectangle. -/
def normalizationFace : ⦋2⦌ ⟶ ⦋17⦌ :=
  SimplexCategory.Hom.mk ⟨![2, 3, 11], by decide⟩

/-- Every characteristic-map point of the shared normalization face agrees literally. -/
theorem normalization_parameter (z : StdSimplex ℝ (Fin 3)) :
    CommonReferenceNerve.parameter (InputTripleNodes.sourceMap c q p)
      (InputTripleNodes.postNode c q p)
      (StdSimplex.map (InputSimplex.triangleFace 1 2 4 (by decide) (by decide)).toOrderHom z) =
    CommonReferenceNerve.parameter (InputTripleNodes.sourceMap c q p)
      (rawNode p q p' q' a b c hp hq)
      (StdSimplex.map normalizationFace.toOrderHom z) := by
  apply CommonReferenceNerve.parameter_eq_of_face_nodes
  intro i
  fin_cases i
  · exact post_total_node p q p' q' a b c hp hq
  · exact post_intermediate_node p q p' q' a b c hp hq
  · exact post_target_node p q p' q' a b c hp hq

/-- The whole original raw rectangle is a compact parameter in the actual common nerve. -/
def rawParameter :=
  (CommonReferenceNerve.parameter (InputTripleNodes.sourceMap c q p)
    (rawNode p q p' q' a b c hp hq)).comp
      BoundedFlatPerfectDoubleSquareScalarPaths.rectangleParameter.toContinuousMap

/-- The whole original evaluation composition face uses the same common nerve. -/
def postParameter :=
  (CommonReferenceNerve.parameter (InputTripleNodes.sourceMap c q p)
    (InputTripleNodes.postNode c q p)).comp InputSimplex.compositionParameter.toContinuousMap

/-- Every point of the raw face evaluates to the unchanged original two-dimensional track. -/
theorem raw_parameter_native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op A))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputTripleNodes.sourceMap c q p)
      (rawParameter p q p' q' a b c hp hq) n ((r, s), x) =
    (boundedAboveFlatPerfectDoubleSquareTrackComparison p q p' q' a b c hp hq).level n
      (r, (s, (prespectrumMap (evaluationModel (op A))).map n x)) := by
  rw [CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ _
    (rawNode p q p' q' a b c hp hq) (r, s)
    (BoundedFlatPerfectDoubleSquareScalarPaths.rectangleParameter (r, s)) rfl]
  change prespectrumSimplexFamily (rawSimplex p q p' q' a b c hp hq) n _ = _
  rw [raw_simplex, prespectrumSimplexFamily_precomp]
  exact BoundedFlatPerfectDoubleSquareScalarPaths.rectangle_native p q p' q' a b c hp hq n r s _

/-- Every point of the postcomposed face keeps the original selected evaluation clocks. -/
theorem post_parameter_native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op A))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputTripleNodes.sourceMap c q p)
      (postParameter p q c) n ((r, s), x) =
    (prespectrumMap (evaluationRawMap c)).map n
      ((evaluationCompositionRelHomotopy q p).level n (r, (s, x))) := by
  rw [CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ _
    (InputTripleNodes.postNode c q p) (r, s)
    (InputSimplex.compositionParameter (r, s)) rfl]
  change prespectrumSimplexFamily (postSimplex p q c) n _ = _
  rw [post_simplex, prespectrumSimplexFamily_postcomp]
  exact congrArg ((prespectrumMap (evaluationRawMap c)).map n)
    (InputSimplex.composition_native q p n r s x)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputRectangleNodes
