/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputRawChartRows
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputRawSquareProduct

/-!
# The actual evaluation-square product attached to the raw chart row

The ten-node product of projection evaluation and the original raw chart square is transported
into the fixed mixed reference. Its entire terminal row agrees as complete dependent nodes with
the projected chart row. Consequently the whole characteristic face and the original square
path agree before native evaluation. The initial row retains its separate original data.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputRawChartProductNodes
open GlobalSectionChangeIndex InputNormalizationPrism InputRawChartRows Topology
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- The complete projected source anchor, with the actual terminal functor association. -/
def terminalAnchor : (InputMixedDesc.sourceMap g).hom.toFunctor ≅
    (firstTarget (projection.app Y) ≫ squareSource g k).hom.toFunctor :=
  (evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y) ≪≫
    isoWhiskerLeft (evaluationModel (op Y)).hom.toFunctor
      (projectionAnchor g k hk ≪≫
        isoWhiskerLeft (evaluationRawMap (projection.app Y)).hom.toFunctor
          (Iso.refl (squareSource g k).hom.toFunctor))) ≪≫
    (Functor.associator (evaluationModel (op Y)).hom.toFunctor
      (evaluationRawMap (projection.app Y)).hom.toFunctor (squareSource g k).hom.toFunctor).symm

/-- The product reference starts at the original projection-evaluation source. -/
def anchor : (InputMixedDesc.sourceMap g).hom.toFunctor ≅
    (firstSource (projection.app Y) ≫ squareSource g k).hom.toFunctor :=
  terminalAnchor g k hk ≪≫
    isoWhiskerRight (evaluationComparisonIso (projection.app Y)).symm
      (squareSource g k).hom.toFunctor

/-- All ten actual composite nodes, with the complete mixed reference retained. -/
def nodes (i : Fin 10) : InputChartReference.Node g :=
  ⟨CommonReferenceProduct.vertices (firstVertices (projection.app Y))
      (InputRawSquareProduct.squareVertices (laurent.map g) (k.app Y)
        (k.app X) (polynomial.map g) (k.naturality g)) i,
    anchor g k hk ≪≫
      CommonReferenceProduct.references (firstSource (projection.app Y))
        (firstVertices (projection.app Y)) (firstAnchors (projection.app Y)) (squareSource g k)
        (InputRawSquareProduct.squareVertices (laurent.map g) (k.app Y)
          (k.app X) (polynomial.map g) (k.naturality g))
        (InputRawSquareProduct.squareAnchors (laurent.map g) (k.app Y)
          (k.app X) (polynomial.map g) (k.naturality g)) i⟩

private theorem cancel_terminal {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    {F₀ F₁ : V ⟶ W} {G₀ G₁ : W ⟶ T} {R : V ⟶ T}
    (a : R.hom.toFunctor ≅ (F₁ ≫ G₀).hom.toFunctor)
    (e : F₀.hom.toFunctor ≅ F₁.hom.toFunctor) (d : G₀.hom.toFunctor ≅ G₁.hom.toFunctor) :
    (a ≪≫ isoWhiskerRight e.symm G₀.hom.toFunctor) ≪≫
      (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso (e.prod d) =
        a ≪≫ isoWhiskerLeft F₁.hom.toFunctor d := by
  rw [CommonReferenceProduct.composition_pair_iso, ← isoWhiskerRight_symm,
    Iso.trans_assoc, Iso.symm_self_id_assoc]

private theorem evaluated_pre_node
  {U V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    (R : U ⟶ T) (Q : V ⟶ T) (E : U ⟶ V) (P : V ⟶ W) (H : W ⟶ T)
    (e : R.hom.toFunctor ≅ (E ≫ Q).hom.toFunctor) (a : Q.hom.toFunctor ≅ (P ≫ H).hom.toFunctor)
    (N : CommonReferenceNerve.Node H) :
    (⟨(E ≫ P) ≫ N.1,
      ((e ≪≫ isoWhiskerLeft E.hom.toFunctor
        (a ≪≫ isoWhiskerLeft P.hom.toFunctor (Iso.refl H.hom.toFunctor))) ≪≫
        (Functor.associator E.hom.toFunctor P.hom.toFunctor H.hom.toFunctor).symm) ≪≫
          isoWhiskerLeft (E ≫ P).hom.toFunctor N.2⟩ : CommonReferenceNerve.Node R) =
    ⟨E ≫ (P ≫ N.1), e ≪≫ isoWhiskerLeft E.hom.toFunctor
      (a ≪≫ isoWhiskerLeft P.hom.toFunctor N.2)⟩ := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  apply NatTrans.ext
  funext A
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, NatTrans.comp_app, whiskerLeft_app,
    Iso.symm_hom, Functor.associator_inv_app, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Category.assoc]
  exact congrArg (fun f => e.hom.app A ≫ a.hom.app (E.hom.toFunctor.obj A) ≫ f)
    (Category.id_comp (N.2.hom.app (P.hom.toFunctor.obj (E.hom.toFunctor.obj A))))

private theorem projected_node (N : CommonReferenceNerve.Node (squareSource g k)) :
    (⟨firstTarget (projection.app Y) ≫ N.1,
      terminalAnchor g k hk ≪≫ isoWhiskerLeft (firstTarget (projection.app Y)).hom.toFunctor N.2⟩ :
        InputChartReference.Node g) = projectedNode g k hk N := by
  unfold terminalAnchor firstTarget projectedNode InputRawDesc.evaluateNode
    ModelSimplex.preReferenceNode
  exact evaluated_pre_node (InputMixedDesc.sourceMap g)
    (GlobalRawBass.InputDescSimplex.reference g) (evaluationModel (op Y))
    (evaluationRawMap (projection.app Y)) (squareSource g k)
    (evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y))
    (projectionAnchor g k hk) N

private theorem product_node_index
  {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} {p q : ℕ}
    (F₀ : V ⟶ W) (F : Fin (p + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.hom.toFunctor ≅ (F i).hom.toFunctor)
    (G₀ : W ⟶ T) (G : Fin (q + 1) → (W ⟶ T))
    (eta : ∀ i, G₀.hom.toFunctor ≅ (G i).hom.toFunctor) (R : V ⟶ T)
    (a : R.hom.toFunctor ≅ (F₀ ≫ G₀).hom.toFunctor) (i : Fin (p + 1)) (j : Fin (q + 1)) :
    (⟨CommonReferenceProduct.vertices F G (SimplexGrid.index p q (i, j)),
      a ≪≫ CommonReferenceProduct.references F₀ F ρ G₀ G eta
        (SimplexGrid.index p q (i, j))⟩ : CommonReferenceNerve.Node R) =
    ⟨F i ≫ G j, a ≪≫
      (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso ((ρ i).prod (eta j))⟩ := by
  unfold CommonReferenceProduct.vertices CommonReferenceProduct.references
  rw [SimplexGrid.decode_index]

/-- Every terminal product node equals the complete original projected square node. -/
theorem terminal_nodes (i : Fin 5) :
    nodes g k hk ((SimplexGrid.rowFace 1 4 1).toOrderHom i) =
      projectedNode g k hk (squareNodes g k i) := by
  change nodes g k hk (SimplexGrid.index 1 4 (1, i)) = _
  unfold nodes
  rw [product_node_index]
  change (⟨firstTarget (projection.app Y) ≫ (squareNodes g k i).1,
    (terminalAnchor g k hk ≪≫
      isoWhiskerRight (evaluationComparisonIso (projection.app Y)).symm
        (squareSource g k).hom.toFunctor) ≪≫
      (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
        ((evaluationComparisonIso (projection.app Y)).prod (squareNodes g k i).2)⟩ :
          InputChartReference.Node g) = _
  rw [cancel_terminal]
  exact projected_node g k hk (squareNodes g k i)

/-- The reanchored model simplex is the unchanged entire original ten-node product. -/
theorem product_simplex :
    ModelSimplex.ofIsos (InputMixedDesc.sourceMap g)
      (fun i => (nodes g k hk i).1) (fun i => (nodes g k hk i).2) =
    InputRawSquareProduct.simplex (laurent.map g) (k.app Y)
      (k.app X) (polynomial.map g) (k.naturality g) (projection.app Y) :=
  ModelSimplex.ofIsos_change_reference (anchor g k hk) _ _

/-- Every point of the terminal characteristic face retains all five complete reference nodes. -/
theorem terminal_face (z : StdSimplex ℝ (Fin 5)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (nodes g k hk)
      (StdSimplex.map (SimplexGrid.rowFace 1 4 1).toOrderHom z) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (fun i => projectedNode g k hk (squareNodes g k i)) z :=
  (CommonReferenceNerve.parameter_face (InputMixedDesc.sourceMap g) (nodes g k hk)
    (SimplexGrid.rowFace 1 4 1) z).trans
    (congrArg (fun N => CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) N z)
      (funext (terminal_nodes g k hk)))

/-- Equality of the entire continuous characteristic maps, before any native evaluation. -/
theorem terminal_characteristic :
    (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (nodes g k hk)).comp
      (⟨StdSimplex.map (SimplexGrid.rowFace 1 4 1).toOrderHom, by fun_prop⟩ :
        C(StdSimplex ℝ (Fin 5), StdSimplex ℝ (Fin 10))) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (fun i => projectedNode g k hk (squareNodes g k i)) := by
  ext z
  exact terminal_face g k hk z

/-- The actual product parameter restricts to the full terminal characteristic row. -/
theorem terminal_grid_parameter (z : StdSimplex ℝ (Fin 5)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (nodes g k hk)
      (SimplexGrid.parameter.{u+1} 1 4 (StdSimplex.single 1, z)) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (fun i => projectedNode g k hk (squareNodes g k i)) z := by
  rw [SimplexGrid.parameter_row]
  exact terminal_face g k hk z

/-- The two original independent times in the fixed mixed common-reference nerve. -/
def parameter :=
  (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (nodes g k hk)).comp
    InputRawSquareProduct.parameter.{u+1}

/-- The terminal evaluation time keeps the entire original reverse-forward square path. -/
theorem terminal_parameter (s : unitInterval) :
    parameter g k hk (1, s) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (fun i => projectedNode g k hk (squareNodes g k i))
      (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) := by
  change CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (nodes g k hk)
    (InputRawSquareProduct.parameter (1, s)) = _
  rw [InputRawSquareProduct.parameter_evaluation_one]
  exact terminal_face g k hk (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s)

/-- The positive terminal square path is exactly the left boundary of the actual raw descent. -/
theorem plus_attachment (s : unitInterval) :
    parameter g plus GlobalRawBass.plus_projection (1, s) = InputRawDesc.parameter g (s, 0) :=
  (terminal_parameter g plus GlobalRawBass.plus_projection s).trans
    (InputRawChartRows.left_parameter g s).symm

/-- The inverse terminal square path is exactly the distinct right raw descent boundary. -/
theorem minus_attachment (s : unitInterval) :
    parameter g minus GlobalRawBass.minus_projection (1, s) = InputRawDesc.parameter g (s, 1) :=
  (terminal_parameter g minus GlobalRawBass.minus_projection s).trans
    (InputRawChartRows.right_parameter g s).symm

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputRawChartProductNodes
