/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvalProduct

/-! Full anchored corners and complete rails of the original evaluation-times-unit surface. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedProductSeams
open GlobalSectionChangeIndex InputNormalizationPrism CommonReferenceNerve
open InputSeedEvaluationProduct

private theorem pair_iso {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
  {F₀ F₁ : V ⟶ W} {G₀ G₁ : W ⟶ T}
    (e : F₀.hom.toFunctor ≅ F₁.hom.toFunctor) (d : G₀.hom.toFunctor ≅ G₁.hom.toFunctor) :
    (Functor.uncurry.obj (whiskeringLeft V.obj.Obj W.obj.Obj T.obj.Obj)).mapIso (e.prod d) =
      isoWhiskerRight e G₀.hom.toFunctor ≪≫ isoWhiskerLeft F₁.hom.toFunctor d := by
  apply Iso.ext
  rfl

private theorem pair_iso_other
    {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    {F₀ F₁ : V ⟶ W} {G₀ G₁ : W ⟶ T}
    (e : F₀.hom.toFunctor ≅ F₁.hom.toFunctor) (d : G₀.hom.toFunctor ≅ G₁.hom.toFunctor) :
    (Functor.uncurry.obj (whiskeringLeft V.obj.Obj W.obj.Obj T.obj.Obj)).mapIso (e.prod d) =
      isoWhiskerLeft F₀.hom.toFunctor d ≪≫ isoWhiskerRight e G₁.hom.toFunctor := by
  apply Iso.ext
  ext A
  exact d.hom.naturality (e.hom.app A)

private theorem source_shift_node
    {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} (R : V ⟶ T)
    (H₀ H₁ : V ⟶ W) (G : W ⟶ T) (η : R.hom.toFunctor ≅ (H₀ ≫ G).hom.toFunctor)
    (ρ : H₀.hom.toFunctor ≅ H₁.hom.toFunctor) (α : G.hom.toFunctor ≅ G.hom.toFunctor)
    (τ : R.hom.toFunctor ≅ R.hom.toFunctor)
    (h : τ ≪≫ η = η ≪≫ isoWhiskerLeft H₀.hom.toFunctor α) :
    (⟨H₁ ≫ G, η ≪≫ (Functor.uncurry.obj (whiskeringLeft V.obj.Obj W.obj.Obj T.obj.Obj)).mapIso
      (ρ.prod α)⟩ : Node R) =
    ModelSimplex.reanchorNode τ
      ⟨H₁ ≫ G, η ≪≫ (Functor.uncurry.obj (whiskeringLeft V.obj.Obj W.obj.Obj T.obj.Obj)).mapIso
        (ρ.prod (Iso.refl _))⟩ := by
  apply congrArg (fun θ ↦ (⟨H₁ ≫ G, θ⟩ : Node R))
  rw [pair_iso_other, pair_iso_other]
  simp only [isoWhiskerLeft_refl, Iso.refl_trans]
  rw [← Iso.trans_assoc, ← h, Iso.trans_assoc]

private theorem first_target {A B C : Scheme.{u}} (f : A ⟶ B) (v : B ⟶ C) :
    evaluationCompositionFirstIso f v ≪≫ evaluationCompositionSecondIso f v =
      evaluationComparisonIso (f ≫ v) ≪≫ evaluationCompositionTargetIso f v := by
  apply Iso.ext
  exact (evaluationComposition_pasting f v).symm

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

private theorem product_node (i j : Fin 2) :
    nodes g (Topology.SimplexGrid.index 1 1 (i, j)) =
      (⟨firstVertices g i ≫ unitMap X, anchor g ≪≫
        (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
          ((firstAnchors g i).prod (unitAnchors X j))⟩ :
        Node (InputSeedCarrier.laurentRef g)) := by
  unfold InputSeedEvaluationProduct.nodes CommonReferenceProduct.vertices
    CommonReferenceProduct.references
  rw [Topology.SimplexGrid.decode_index]
  rfl

private theorem terminal_anchor :
    anchor g ≪≫ isoWhiskerRight (evaluationComparisonIso g) (unitMap X).hom.toFunctor =
      (InputSeedUnitNodes.lower g 7).2 := by
  change (InputCommutingSimplex.sourceIso (laurent.map g)
      (GlobalRawBass.laurentProjection.app Y) (GlobalRawBass.laurentProjection.app X) g
      (GlobalRawBass.laurentProjection.naturality g) ≪≫
        evaluationCompositionFirstIso (GlobalRawBass.laurentProjection.app X) g) ≪≫
      evaluationCompositionSecondIso (GlobalRawBass.laurentProjection.app X) g = _
  rw [Iso.trans_assoc, first_target]
  rfl

set_option backward.isDefEq.respectTransparency true in
/-- The product begins at the entire original lower evaluation cut. -/
theorem zero_node : nodes g 0 = InputSeedUnitNodes.lower g 6 := by
  change nodes g (Topology.SimplexGrid.index 1 1 (0, 0)) = _
  rw [product_node]
  change (⟨firstSource g ≫ unitMap X, anchor g ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((Iso.refl (firstSource g).hom.toFunctor).prod (Iso.refl (unitMap X).hom.toFunctor))⟩ :
      Node (InputSeedCarrier.laurentRef g)) = _
  rw [pair_iso, isoWhiskerRight_refl, isoWhiskerLeft_refl, Iso.refl_trans]
  refine (congrArg (fun e ↦ (⟨firstSource g ≫ unitMap X, e⟩ :
    Node (InputSeedCarrier.laurentRef g))) (Iso.trans_refl (anchor g))).trans ?_
  rfl


/-- The other lower corner keeps the original evaluation composition reference word. -/
theorem two_node : nodes g 2 = InputSeedUnitNodes.lower g 7 := by
  change nodes g (Topology.SimplexGrid.index 1 1 (1, 0)) = _
  rw [product_node]
  simp only [firstAnchors, unitAnchors,
    Matrix.cons_val_zero, pair_iso, isoWhiskerLeft_refl, Iso.trans_refl]
  exact congrArg (fun e ↦ (⟨firstTarget g ≫ unitMap X, e⟩ :
    Node (InputSeedCarrier.laurentRef g))) (terminal_anchor g)

set_option backward.isDefEq.respectTransparency true in
private theorem anchor_unit :
    InputSeedCarrier.commonUnit g ≪≫ anchor g =
      anchor g ≪≫ isoWhiskerLeft (firstSource g).hom.toFunctor (unitIso X) :=
  InputSeedCarrier.anchor_unit g ⟨firstSource g ≫ unitMap X, anchor g⟩

/-- Both upper corners keep the same actual common-unit shift before any native evaluation. -/
theorem shifted_node (i : Fin 2) :
    nodes g (Topology.SimplexGrid.index 1 1 (i, 1)) =
      ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g)
        (nodes g (Topology.SimplexGrid.index 1 1 (i, 0))) := by
  rw [product_node, product_node]
  exact source_shift_node (InputSeedCarrier.laurentRef g) (firstSource g)
    (firstVertices g i) (unitMap X) (anchor g) (firstAnchors g i) (unitIso X)
    (InputSeedCarrier.commonUnit g) (anchor_unit g)

/-- The first upper corner is the full original shifted cut. -/
theorem one_node : nodes g 1 = InputSeedUnitNodes.upper g 6 :=
  (shifted_node g 0).trans
    (congrArg (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g)) (zero_node g))

/-- The terminal upper corner is the full original shifted target. -/
theorem three_node : nodes g 3 = InputSeedUnitNodes.upper g 7 :=
  (shifted_node g 1).trans
    (congrArg (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g)) (two_node g))

/-- The four actual full references inside the sixteen-node Laurent unit diagram. -/
def cornerIndex : Fin 4 → Fin 16 := ![6, 14, 7, 15]

/-- Corner identification retains both Model arrows and their complete reference isomorphisms. -/
theorem corners (i : Fin 4) : nodes g i = InputSeedUnitNodes.nodes g (cornerIndex i) := by
  fin_cases i
  · exact zero_node g
  · exact one_node g
  · exact two_node g
  · exact three_node g

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedProductSeams
