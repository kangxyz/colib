/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartReference

/-!
# The original raw rectangle in the mixed Laurent reference

The proved chart projection equation reanchors the complete original rectangle without
changing any point of its native two-dimensional family or its selected normalization face.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartReference
open GlobalSectionChangeIndex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- The original two-dimensional raw rectangle, with its complete mixed reference. -/
def rawParameter :=
  (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (rawNode g k hk)).comp
    BoundedFlatPerfectDoubleSquareScalarPaths.rectangleParameter.toContinuousMap

/-- Every native point is the unchanged original geometric double-square comparison. -/
theorem raw_parameter_native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (rawParameter g k hk) n ((r, s), x) =
    (boundedAboveFlatPerfectDoubleSquareTrackComparison (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g)).level n
        (r, (s, (prespectrumMap (evaluationModel (op Y))).map n x)) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ _
    (rawNode g k hk) (r, s)
    (BoundedFlatPerfectDoubleSquareScalarPaths.rectangleParameter (r, s)) rfl n x).trans ?_
  have h := congrArg
    (fun T => prespectrumSimplexFamily T n
      (BoundedFlatPerfectDoubleSquareScalarPaths.rectangleParameter (r, s), x))
    (ModelSimplex.reanchorSimplex_eq (chartSourceIso g k hk)
      (InputRectangleNodes.rawNode (projection.app Y) (k.app Y)
        (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
        (projection.naturality g) (k.naturality g)))
  refine h.trans ?_
  exact (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
    (InputTripleNodes.sourceMap (laurent.map g) (k.app Y) (projection.app Y))
    (InputRectangleNodes.rawParameter (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g))
    (InputRectangleNodes.rawNode (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g)) (r, s)
    (BoundedFlatPerfectDoubleSquareScalarPaths.rectangleParameter (r, s)) rfl n x).symm.trans
      (InputRectangleNodes.raw_parameter_native (projection.app Y) (k.app Y)
        (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
        (projection.naturality g) (k.naturality g) n r s x)

/-- The original total Y node is the full second raw rectangle node in the mixed reference. -/
theorem post_total_node : postNode g k hk 1 = rawNode g k hk 2 :=
  congrArg (fun N : InputTripleNodes.Node (laurent.map g) (k.app Y) (projection.app Y) =>
    (⟨N.1, chartSourceIso g k hk ≪≫ N.2⟩ : Node g))
    (InputRectangleNodes.post_total_node (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g))

/-- The actual geometric Y intermediate is the full third raw node. -/
theorem post_intermediate_node : postNode g k hk 2 = rawNode g k hk 3 :=
  congrArg (fun N : InputTripleNodes.Node (laurent.map g) (k.app Y) (projection.app Y) =>
    (⟨N.1, chartSourceIso g k hk ≪≫ N.2⟩ : Node g))
    (InputRectangleNodes.post_intermediate_node (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g))

/-- The original split Y target is exactly full raw rectangle node eleven. -/
theorem post_target_node : postNode g k hk 4 = rawNode g k hk 11 :=
  congrArg (fun N : InputTripleNodes.Node (laurent.map g) (k.app Y) (projection.app Y) =>
    (⟨N.1, chartSourceIso g k hk ≪≫ N.2⟩ : Node g))
    (InputRectangleNodes.post_target_node (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g))

/-- The entire shared normalization characteristic face agrees before native evaluation. -/
theorem normalization_parameter (z : StdSimplex ℝ (Fin 3)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (postNode g k hk)
      (StdSimplex.map (InputSimplex.triangleFace 1 2 4 (by decide) (by decide)).toOrderHom z) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (rawNode g k hk)
      (StdSimplex.map InputRectangleNodes.normalizationFace.toOrderHom z) := by
  apply CommonReferenceNerve.parameter_eq_of_face_nodes
  intro i
  fin_cases i
  · exact post_total_node g k hk
  · exact post_intermediate_node g k hk
  · exact post_target_node g k hk

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartReference
