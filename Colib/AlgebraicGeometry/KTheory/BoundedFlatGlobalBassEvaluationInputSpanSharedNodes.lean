/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartRawFace
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumProjectionReference

/-!
# The five complete shared nodes of the original raw input rectangles

Both original chart rectangles have the same outer-projection path, with vertex word
`2, 1, 0, 14, 15`. The full dependent nodes at these five indices agree in the fixed mixed
Laurent reference. Their original Model arrows and evaluation anchors are retained; the
other thirteen nodes of each chart remain separate.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanSharedNodes
open GlobalSectionChangeIndex GlobalRawBass SmallWaldhausenCategory
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

private def evaluateProjectionNode {A C D : Scheme.{u}} (c : D ⟶ C) (r : C ⟶ A)
    (N : BoundedFlatPerfectProjectionReference.Node c r) :
    Σ F : boundedAboveFlatGlobalSectionModelFunctor.obj (op A) ⟶
      asSmallCategory (boundedAboveFlatPerfectWaldhausen D.toRingedSpace),
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

/-- Evaluate a complete geometric outer-reference node with the original total comparison. -/
def evaluateNode
    (N : BoundedFlatPerfectProjectionReference.Node (laurent.map g) (laurentProjection.app Y)) :
    InputChartReference.Node g :=
  ⟨evaluationModel (op Y) ≫ N.1,
    evaluationComparisonIso (laurent.map g ≫ laurentProjection.app Y) ≪≫
      isoWhiskerLeft (evaluationModel (op Y)).hom.toFunctor N.2⟩

private theorem reanchor_refl_family {U V : WideSubcategory preservesZero.{u}} {F : U ⟶ V} {n : ℕ}
    (N : Fin (n + 1) → Σ G : U ⟶ V, F.hom.toFunctor ≅ G.hom.toFunctor) :
    ModelSimplex.reanchorNodes (Iso.refl F.hom.toFunctor) N = N := by
  funext i
  dsimp only [ModelSimplex.reanchorNodes, ModelSimplex.reanchorNode]
  rw [Iso.refl_trans]

private theorem evaluate_reference_family {A B C D : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (c : D ⟶ C) (r : C ⟶ A) (hr : q ≫ p = r)
    {n : ℕ} (N : Fin (n + 1) → BoundedFlatPerfectDoubleSquareCommonSimplex.Node p q c) :
    ModelSimplex.reanchorNodes
      (F₀ := boundedAboveFlatGlobalSectionModelFunctor.map (c ≫ r).op ≫ evaluationModel (op D))
      (F₁ := InputTripleNodes.sourceMap c q p)
      (eqToIso (congrArg (fun j : D ⟶ A =>
        (boundedAboveFlatGlobalSectionModelFunctor.map j.op ≫ evaluationModel (op D)).hom.toFunctor)
          (congrArg (fun j ↦ c ≫ j) hr).symm))
      (fun i ↦ evaluateTripleNode p q c (N i)) =
    fun i ↦ evaluateProjectionNode c r
      (ModelSimplex.reanchorNodes
        (F₀ := BoundedFlatPerfectProjectionReference.reference c r)
        (F₁ := BoundedFlatPerfectTripleSimplex.source c q p)
        (eqToIso (BoundedFlatPerfectProjectionReference.anchor p q c r hr)) N i) := by
  subst r
  change ModelSimplex.reanchorNodes (Iso.refl (InputTripleNodes.sourceMap c q p).hom.toFunctor)
      (fun i ↦ evaluateTripleNode p q c (N i)) =
    fun i ↦ evaluateProjectionNode c (q ≫ p)
      (ModelSimplex.reanchorNodes
        (Iso.refl (BoundedFlatPerfectTripleSimplex.source c q p).hom.toFunctor) N i)
  rw [reanchor_refl_family]
  exact (congrArg
    (fun M : Fin (n + 1) → BoundedFlatPerfectDoubleSquareCommonSimplex.Node p q c ↦
      fun i ↦ evaluateProjectionNode c (q ≫ p) (M i))
    (@reanchor_refl_family (asSmallCategory (boundedAboveFlatPerfectWaldhausen A.toRingedSpace))
      (asSmallCategory (boundedAboveFlatPerfectWaldhausen D.toRingedSpace))
      (BoundedFlatPerfectTripleSimplex.source c q p) n N)).symm

private theorem raw_rectangle_evaluated {A B C A' B' C' : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
    (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
    (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b) :
    InputRectangleNodes.rawNode p q p' q' a b c hp hq =
      fun i ↦ evaluateTripleNode p q c
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
          (congrArg (fun j ↦ c ≫ j) hr).symm))
      (InputRectangleNodes.rawNode p q p' q' a b c hp hq) =
    fun i ↦ evaluateProjectionNode c r
      (BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr i) := by
  rw [raw_rectangle_evaluated, projection_nodes_reanchored]
  exact evaluate_reference_family p q c r hr
    (BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq)

variable (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = laurentProjection.app Z)

/-- The complete original chart family is evaluated from its geometric projection family.
The reference change is exactly the actual chart projection equation. -/
theorem raw_node_evaluate_family :
    InputChartReference.rawNode g k hk =
      fun i ↦ evaluateNode g
        (BoundedFlatPerfectProjectionReference.nodes (projection.app Y) (k.app Y)
          (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
          (projection.naturality g) (k.naturality g)
          (laurentProjection.app Y) (hk Y) i) := by
  exact raw_rectangle_family (projection.app Y) (k.app Y)
    (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
    (projection.naturality g) (k.naturality g) (laurentProjection.app Y) (hk Y)

/-- Every full original chart node keeps that same geometric evaluation transport. -/
theorem raw_node_evaluate (i : Fin 18) :
    InputChartReference.rawNode g k hk i =
      evaluateNode g
        (BoundedFlatPerfectProjectionReference.nodes (projection.app Y) (k.app Y)
          (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
          (projection.naturality g) (k.naturality g)
          (laurentProjection.app Y) (hk Y) i) :=
  congrFun (raw_node_evaluate_family g k hk) i

/-- Every valid chart factorization has the same five evaluated outer reference nodes. -/
theorem shared_nodes (l : laurent ⟶ polynomial)
    (hl : ∀ Z, l.app Z ≫ projection.app Z = laurentProjection.app Z) (i : Fin 5) :
    InputChartReference.rawNode g k hk (BoundedFlatPerfectProjectionReference.sharedIndex i) =
      InputChartReference.rawNode g l hl (BoundedFlatPerfectProjectionReference.sharedIndex i) := by
  let j := BoundedFlatPerfectProjectionReference.sharedIndex i
  exact (raw_node_evaluate g k hk j).trans
    ((congrArg (evaluateNode g) (BoundedFlatPerfectProjectionReference.two_projection_shared
      (projection.app Y) (k.app Y) (projection.app X) (k.app X) g
      (polynomial.map g) (laurent.map g) (projection.naturality g) (k.naturality g)
      (laurentProjection.app Y) (laurentProjection.app X) (hk Y) (hk X)
      (l.app Y) (l.app X) (l.naturality g) (hl Y) (hl X) i)).trans
      (raw_node_evaluate g l hl j).symm)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanSharedNodes
