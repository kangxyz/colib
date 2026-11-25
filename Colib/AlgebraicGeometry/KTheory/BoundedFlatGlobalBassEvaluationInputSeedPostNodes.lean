/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedPostProduct
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedPostUnit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputRawPastedSeam
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanTargetColumn
public import Colib.KTheory.Waldhausen.Iterated.ReferenceWhiskeringFamily

/-!
# Complete endpoint attachments of the original raw seed postproduct

The original source polynomial node pins both columns of the actual raw chart square. Full
reference-family cancellation extends those exact joins to every polynomial node. The second
sheet uses the same original forward Laurent unit and actual raw postcomposition reference.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CategoryTheory.Waldhausen.IteratedS Topology SSet
open CategoryTheory.Waldhausen SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedPostNodes
open GlobalSectionChangeIndex CommonReferenceNerve ModelSimplex

private theorem product_post {V W T : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (R : W ⟶ T)
    (G : V ⟶ T) (a : G.hom.toFunctor ≅ (F ≫ R).hom.toFunctor) (N : Node F) (M : Node R) :
    InputSeedPostProduct.composedNode G F R a N M =
      postReferenceNode G M.1 (a ≪≫ isoWhiskerLeft F.hom.toFunctor M.2) N := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  change a ≪≫ (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso (N.2.prod M.2) =
    (a ≪≫ isoWhiskerLeft F.hom.toFunctor M.2) ≪≫ isoWhiskerRight N.2 M.1.hom.toFunctor
  rw [CommonReferenceProduct.composition_pair_iso_other, Iso.trans_assoc]

private theorem post_source {V W T : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (R : W ⟶ T)
    (G : V ⟶ T) (a : G.hom.toFunctor ≅ (F ≫ R).hom.toFunctor) :
    attachPostcompNode F R G a ⟨F, Iso.refl _⟩ = (⟨F ≫ R, a⟩ : Node G) := by
  apply congrArg (fun e => (⟨F ≫ R, e⟩ : Node G))
  change a ≪≫ isoWhiskerRight (Iso.refl F.hom.toFunctor) R.hom.toFunctor = a
  exact (congrArg (fun e => a ≪≫ e) (isoWhiskerRight_refl F.hom.toFunctor R.hom.toFunctor)).trans
    (Iso.trans_refl a)

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
local notation "F" => InputSeedEvaluationCarrier.polyRef Y
local notation "G" => InputSeedCarrier.laurentRef g
local notation "R" => InputRawChartRows.squareSource g plus

/-- The original polynomial cut fixes the complete source anchor before chart attachment. -/
def polynomialSourceIso : (InputSeedCarrier.polyRef g).hom.toFunctor ≅
    (F ≫ evaluationRawMap (polynomial.map g)).hom.toFunctor :=
  (InputSpanParameterNodes.projectionNodes g 3).2

/-- Every polynomial node is postcomposed by its actual normalized geometric map. -/
def polynomialNode := attachPostcompNode F (evaluationRawMap (polynomial.map g))
  (InputSeedCarrier.polyRef g) (polynomialSourceIso g)

/-- The original ordinary chart attachment on the entire objectwise polynomial family. -/
def originalOrdinaryNode := attachPostcompNode F (InputSeedEvaluationCarrier.chart Y)
  (InputSeedEvaluationCarrier.laurentRef Y) (InputSeedEvaluationCarrier.ordinary Y)

/-- The unchanged ordinary chart attachment on the mixed polynomial family. -/
def ordinaryNode := attachPostcompNode (InputSeedCarrier.polyRef g)
  (InputSeedCarrier.chart (X := X)) G (InputSeedCarrier.ordinary g)

/-- The original source node lands at precisely the original polynomial projection cut. -/
theorem polynomial_zero : polynomialNode g (InputSeedEvaluationCarrier.polynomialNodes Y 0) =
    InputSpanParameterNodes.projectionNodes g 3 :=
  post_source F (evaluationRawMap (polynomial.map g))
    (InputSeedCarrier.polyRef g) (polynomialSourceIso g)

/-- The original terminal polynomial evaluation node retains its complete projection anchor. -/
theorem polynomial_one : polynomialNode g (InputSeedEvaluationCarrier.polynomialNodes Y 1) =
    InputSpanParameterNodes.projectionNodes g 4 := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  change evaluationCompositionFirstIso (polynomial.map g) (projection.app Y) ≪≫
      evaluationCompositionSecondIso (polynomial.map g) (projection.app Y) =
    evaluationComparisonIso (polynomial.map g ≫ projection.app Y) ≪≫
      evaluationCompositionTargetIso (polynomial.map g) (projection.app Y)
  exact Iso.ext (evaluationComposition_pasting (polynomial.map g) (projection.app Y)).symm

/-- Both complete original polynomial rows give the unchanged ten-node raw product. -/
theorem product_nodes (i : Fin 2) (j : Fin 5) :
    InputSeedPostProduct.productNode g (InputSeedEvaluationCarrier.polynomialNodes Y i) j =
      InputRawChartProductNodes.nodes g plus GlobalRawBass.plus_projection
        (Topology.SimplexGrid.index 1 4 (i, j)) := by
  unfold InputSeedPostProduct.productNode InputSeedPostProduct.composedNode
    InputRawChartProductNodes.nodes CommonReferenceProduct.vertices
    CommonReferenceProduct.references
  rw [Topology.SimplexGrid.decode_index]; rfl

/-- The source raw column retains the full original postcomposed ordinary source node. -/
theorem ordinary_source_zero :
    InputSeedPostProduct.productNode g (InputSeedEvaluationCarrier.polynomialNodes Y 0) 2 =
      InputMixedDesc.postNode g
        (originalOrdinaryNode (Y := Y) (InputSeedEvaluationCarrier.polynomialNodes Y 0)) :=
  (product_nodes g 0 2).trans
    ((InputRawPastedSeam.column_initial_node g plus GlobalRawBass.plus_projection).trans
      ((InputChartReference.post_nodes g plus GlobalRawBass.plus_projection 3).trans
        (congrArg (InputMixedDesc.postNode g) (InputSeedEvaluationCarrier.polynomial_nodes Y 0))))

/-- The terminal raw column retains the actual chart-attached polynomial projection cut. -/
theorem ordinary_target_zero :
    InputSeedPostProduct.productNode g (InputSeedEvaluationCarrier.polynomialNodes Y 0) 4 =
      ordinaryNode g (polynomialNode g (InputSeedEvaluationCarrier.polynomialNodes Y 0)) := by
  rw [polynomial_zero]
  exact (product_nodes g 0 4).trans
    (InputSpanTargetColumn.column_initial_node g plus GlobalRawBass.plus_projection).symm

attribute [local irreducible] InputRawChartProductNodes.anchor
  InputSeedEvaluationCarrier.ordinary InputSeedCarrier.ordinary
  InputMixedDesc.postSourceIso polynomialSourceIso

/-- Every complete source-column node keeps the original ordinary postattachment. -/
theorem ordinary_source (N : Node F) : InputSeedPostProduct.productNode g N 2 =
    InputMixedDesc.postNode g (originalOrdinaryNode (Y := Y) N) :=
  post_families_match G
    (InputSeedEvaluationCarrier.chart Y ≫ evaluationRawMap (laurent.map g)) F (fun M => M)
    (fun M => product_post F R G
      (InputRawChartProductNodes.anchor g plus GlobalRawBass.plus_projection) M
      (BoundedFlatPerfectNativeSquareFiveSimplex.nodes (laurent.map g) (plus.app Y) (plus.app X)
        (polynomial.map g) (plus.naturality g) 2))
    (fun M => post_post_node G (InputSeedEvaluationCarrier.chart Y)
      (evaluationRawMap (laurent.map g)) F (InputSeedEvaluationCarrier.ordinary Y)
      (InputMixedDesc.postSourceIso g) M)
    (InputSeedEvaluationCarrier.polynomialNodes Y 0) (ordinary_source_zero g) N

/-- Every complete terminal-column node keeps the original mixed ordinary attachment. -/
theorem ordinary_target (N : Node F) : InputSeedPostProduct.productNode g N 4 =
    ordinaryNode g (polynomialNode g N) :=
  post_families_match G
    (evaluationRawMap (polynomial.map g) ≫ InputSeedCarrier.chart (X := X)) F (fun M => M)
    (fun M => product_post F R G
      (InputRawChartProductNodes.anchor g plus GlobalRawBass.plus_projection) M
      (BoundedFlatPerfectNativeSquareFiveSimplex.nodes (laurent.map g) (plus.app Y) (plus.app X)
        (polynomial.map g) (plus.naturality g) 4))
    (fun M => post_post_node G (evaluationRawMap (polynomial.map g))
      (InputSeedCarrier.chart (X := X)) F (polynomialSourceIso g) (InputSeedCarrier.ordinary g) M)
    (InputSeedEvaluationCarrier.polynomialNodes Y 0) (ordinary_target_zero g) N

/-- The original unit-shifted chart attachment on the objectwise polynomial family. -/
def originalShiftedNode := attachPostcompNode F (InputSeedEvaluationCarrier.chart Y)
  (InputSeedEvaluationCarrier.laurentRef Y) (InputSeedEvaluationCarrier.shifted Y)

/-- The same original shifted chart attachment on the mixed polynomial family. -/
def shiftedNode := attachPostcompNode (InputSeedCarrier.polyRef g)
  (InputSeedCarrier.chart (X := X)) G (InputSeedCarrier.shifted g)

/-- Every shifted source-column node retains the actual raw postmap and the original unit. -/
theorem shifted_source (N : Node F) :
    ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g)
        (InputSeedPostProduct.productNode g N 2) =
      InputMixedDesc.postNode g (originalShiftedNode (Y := Y) N) :=
  (congrArg (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g))
    (ordinary_source g N)).trans
      ((InputSeedPostUnit.post_shift g (originalOrdinaryNode (Y := Y) N)).trans
        (congrArg (InputMixedDesc.postNode g)
          (reanchor_attach_node F (InputSeedEvaluationCarrier.chart Y)
            (InputSeedEvaluationCarrier.laurentRef Y) (InputSeedEvaluationCarrier.commonUnit Y)
            (InputSeedEvaluationCarrier.ordinary Y) N)))

/-- Every shifted terminal-column node keeps its original mixed attachment anchor. -/
theorem shifted_target (N : Node F) :
    ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g)
        (InputSeedPostProduct.productNode g N 4) =
      shiftedNode g (polynomialNode g N) :=
  (congrArg (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g))
    (ordinary_target g N)).trans (InputSeedCarrier.shifted_node g (polynomialNode g N))

/-- The source-column map equality retains every original polynomial nerve point. -/
theorem ordinary_source_mapParameter (y : |nerve (Codiscrete (Node F))|) :
    mapParameter (fun N => InputSeedPostProduct.productNode g N 2) y =
      mapParameter (InputMixedDesc.postNode g)
        (mapParameter (originalOrdinaryNode (Y := Y)) y) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter F y
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun ns => parameter G ns z) (funext fun i => ordinary_source g (N i))

/-- The terminal-column map equality retains every original polynomial nerve point. -/
theorem ordinary_target_mapParameter (y : |nerve (Codiscrete (Node F))|) :
    mapParameter (fun N => InputSeedPostProduct.productNode g N 4) y =
      mapParameter (ordinaryNode g) (mapParameter (polynomialNode g) y) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter F y
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun ns => parameter G ns z)
    (funext fun i => ordinary_target g (N i))

/-- The whole raw-square parameter starts at the original ordinary postattachment. -/
theorem ordinary_source_parameter (y : |nerve (Codiscrete (Node F))|) :
    InputSeedPostProduct.parameter g (y, 0) =
      mapParameter (InputMixedDesc.postNode g) (mapParameter (originalOrdinaryNode (Y := Y)) y) :=
  (InputSeedPostProduct.parameter_zero g y).trans (ordinary_source_mapParameter g y)

/-- The whole raw-square parameter ends at the original mixed ordinary attachment. -/
theorem ordinary_target_parameter (y : |nerve (Codiscrete (Node F))|) :
    InputSeedPostProduct.parameter g (y, 1) =
      mapParameter (ordinaryNode g) (mapParameter (polynomialNode g) y) :=
  (InputSeedPostProduct.parameter_one g y).trans (ordinary_target_mapParameter g y)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedPostNodes
