/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartSquareParameter
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputNormalizationPrism
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSquareFiveSimplex
public import Colib.KTheory.Waldhausen.Iterated.ReferenceWhiskeringFamily
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputRawChartProductNodes

/-!
# Complete normalization rows of the chart square and evaluation product

The five normalization nodes of each original commuting chart square are fixed precompositions
of its actual normalized raw square. Each identity preserves the full reference anchor,
including the equality transport in the second normalization route.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartNormalizationNodes
open GlobalSectionChangeIndex ModelSimplex Topology

attribute [local irreducible] evaluationComparisonIso evaluationCompositionTargetIso

/-- The five original normalization nodes in their eight-node commuting square. -/
def normalizationRow : Fin 5 → Fin 8 := ![1, 2, 4, 5, 7]

private theorem node_anchor_congr
    {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} {F : V ⟶ W}
    {N M : CommonReferenceNerve.Node F} (e : N = M)
    (h : N.1.hom.toFunctor = M.1.hom.toFunctor) : N.2 ≪≫ eqToIso h = M.2 := by
  cases e
  simp

private theorem whisker_eqToIso {A B C : Type*}
    [Category A] [Category B] [Category C]
    (F : A ⥤ B) {G H : B ⥤ C} (e : G = H) :
    isoWhiskerLeft F (eqToIso e) = eqToIso (congrArg (fun K => F ⋙ K) e) := by
  cases e
  rfl

private theorem commuting_normalization_anchor {A B C D : Scheme.{u}}
    (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
    (h : p ≫ v = q ≫ w) :
    evaluationComparisonIso (p ≫ v) ≪≫
        isoWhiskerLeft (evaluationModel (op C)).hom.toFunctor
          (BoundedFlatPerfectNativeSquareFiveSimplex.sourceIso p v q w h) =
      InputCommutingSimplex.sourceIso p v q w h ≪≫ evaluationComparisonIso (q ≫ w) := by
  have he := node_anchor_congr (InputCommutingSimplex.secondNodes_one p v q w h).symm
    (congrArg (fun H => (evaluationModel (op C)).hom.toFunctor ⋙ H)
      (BoundedFlatPerfectNativeSquareFiveSimplex.source_eq p v q w h))
  unfold BoundedFlatPerfectNativeSquareFiveSimplex.sourceIso
  rw [whisker_eqToIso]
  exact he

private theorem commuting_normalization_node_0 {A B C D : Scheme.{u}}
    (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
    (h : p ≫ v = q ≫ w) :
    InputCommutingSimplex.nodes p v q w h (normalizationRow 0) =
      preReferenceNode (InputCommutingSimplex.sourceMap p v) (evaluationModel (op C))
        (evaluationComparisonIso (p ≫ v))
          (BoundedFlatPerfectNativeSquareFiveSimplex.nodes p v q w h 0) := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change (evaluationComparisonIso (p ≫ v)).hom =
    (evaluationComparisonIso (p ≫ v) ≪≫ isoWhiskerLeft _ (Iso.refl _)).hom
  apply NatTrans.ext
  funext x
  exact (Category.comp_id _).symm

private theorem commuting_normalization_node_1 {A B C D : Scheme.{u}}
    (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
    (h : p ≫ v = q ≫ w) :
    InputCommutingSimplex.nodes p v q w h (normalizationRow 1) =
      preReferenceNode (InputCommutingSimplex.sourceMap p v) (evaluationModel (op C))
        (evaluationComparisonIso (p ≫ v))
          (BoundedFlatPerfectNativeSquareFiveSimplex.nodes p v q w h 1) := by
  rfl

private theorem commuting_normalization_node_2 {A B C D : Scheme.{u}}
    (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
    (h : p ≫ v = q ≫ w) :
    InputCommutingSimplex.nodes p v q w h (normalizationRow 2) =
      preReferenceNode (InputCommutingSimplex.sourceMap p v) (evaluationModel (op C))
        (evaluationComparisonIso (p ≫ v))
          (BoundedFlatPerfectNativeSquareFiveSimplex.nodes p v q w h 2) := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change (evaluationComparisonIso (p ≫ v) ≪≫ evaluationCompositionTargetIso p v).hom = _
  rw [InputNormalizationPrism.normalization_target]
  rfl

private theorem whiskered_reference_hom
    {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    {F R : V ⟶ T} (E : V ⟶ W) {G H K : W ⟶ T}
    (ρ : F.hom.toFunctor ≅ (E ≫ G).hom.toFunctor) (σ : F.hom.toFunctor ≅ R.hom.toFunctor)
    (τ : R.hom.toFunctor ≅ (E ≫ H).hom.toFunctor) (η : G.hom.toFunctor ≅ H.hom.toFunctor)
    (δ : H.hom.toFunctor ≅ K.hom.toFunctor)
    (h : ρ ≪≫ isoWhiskerLeft E.hom.toFunctor η = σ ≪≫ τ) :
    (σ ≪≫ (τ ≪≫ isoWhiskerLeft E.hom.toFunctor δ)).hom =
      (ρ ≪≫ isoWhiskerLeft E.hom.toFunctor (η ≪≫ δ)).hom := by
  apply congrArg Iso.hom
  calc
    _ = (σ ≪≫ τ) ≪≫ isoWhiskerLeft E.hom.toFunctor δ := (Iso.trans_assoc _ _ _).symm
    _ = (ρ ≪≫ isoWhiskerLeft E.hom.toFunctor η) ≪≫ isoWhiskerLeft E.hom.toFunctor δ :=
      congrArg (fun e => e ≪≫ isoWhiskerLeft E.hom.toFunctor δ) h.symm
    _ = ρ ≪≫ (isoWhiskerLeft E.hom.toFunctor η ≪≫ isoWhiskerLeft E.hom.toFunctor δ) :=
      Iso.trans_assoc _ _ _
    _ = _ := congrArg (fun e => ρ ≪≫ e) (isoWhiskerLeft_trans E.hom.toFunctor η δ).symm

private theorem commuting_normalization_node_3 {A B C D : Scheme.{u}}
    (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
    (h : p ≫ v = q ≫ w) :
    InputCommutingSimplex.nodes p v q w h (normalizationRow 3) =
      preReferenceNode (InputCommutingSimplex.sourceMap p v) (evaluationModel (op C))
        (evaluationComparisonIso (p ≫ v))
          (BoundedFlatPerfectNativeSquareFiveSimplex.nodes p v q w h 3) := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change (InputCommutingSimplex.sourceIso p v q w h ≪≫
    (evaluationComparisonIso (q ≫ w) ≪≫
      isoWhiskerLeft (evaluationModel (op C)).hom.toFunctor
        (BoundedFlatPerfectBinarySimplex.first q w))).hom =
    (evaluationComparisonIso (p ≫ v) ≪≫
      isoWhiskerLeft (evaluationModel (op C)).hom.toFunctor
        (BoundedFlatPerfectNativeSquareFiveSimplex.sourceIso p v q w h ≪≫
          BoundedFlatPerfectBinarySimplex.first q w)).hom
  exact whiskered_reference_hom (evaluationModel (op C))
    (evaluationComparisonIso (p ≫ v)) (InputCommutingSimplex.sourceIso p v q w h)
    (evaluationComparisonIso (q ≫ w))
      (BoundedFlatPerfectNativeSquareFiveSimplex.sourceIso p v q w h)
    (BoundedFlatPerfectBinarySimplex.first q w) (commuting_normalization_anchor p v q w h)

private theorem commuting_normalization_node_4 {A B C D : Scheme.{u}}
    (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
    (h : p ≫ v = q ≫ w) :
    InputCommutingSimplex.nodes p v q w h (normalizationRow 4) =
      preReferenceNode (InputCommutingSimplex.sourceMap p v) (evaluationModel (op C))
        (evaluationComparisonIso (p ≫ v))
          (BoundedFlatPerfectNativeSquareFiveSimplex.nodes p v q w h 4) := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change (InputCommutingSimplex.sourceIso p v q w h ≪≫
    (evaluationComparisonIso (q ≫ w) ≪≫ evaluationCompositionTargetIso q w)).hom =
    (evaluationComparisonIso (p ≫ v) ≪≫
      isoWhiskerLeft (evaluationModel (op C)).hom.toFunctor
        (BoundedFlatPerfectNativeSquareFiveSimplex.sourceIso p v q w h ≪≫
          BoundedFlatPerfectBinarySimplex.total q w)).hom
  rw [InputNormalizationPrism.normalization_target]
  exact whiskered_reference_hom (evaluationModel (op C))
    (evaluationComparisonIso (p ≫ v)) (InputCommutingSimplex.sourceIso p v q w h)
    (evaluationComparisonIso (q ≫ w))
      (BoundedFlatPerfectNativeSquareFiveSimplex.sourceIso p v q w h)
    (BoundedFlatPerfectBinarySimplex.total q w) (commuting_normalization_anchor p v q w h)

/-- Each complete original normalization node retains its actual evaluation attachment. -/
theorem commuting_normalization_nodes {A B C D : Scheme.{u}}
    (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
    (h : p ≫ v = q ≫ w) (i : Fin 5) :
    InputCommutingSimplex.nodes p v q w h (normalizationRow i) =
      preReferenceNode (InputCommutingSimplex.sourceMap p v) (evaluationModel (op C))
        (evaluationComparisonIso (p ≫ v))
          (BoundedFlatPerfectNativeSquareFiveSimplex.nodes p v q w h i) := by
  fin_cases i
  · exact commuting_normalization_node_0 p v q w h
  · exact commuting_normalization_node_1 p v q w h
  · exact commuting_normalization_node_2 p v q w h
  · exact commuting_normalization_node_3 p v q w h
  · exact commuting_normalization_node_4 p v q w h

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- The chart row retains its actual first normalization node as the complete anchor. -/
def chartAnchor : (InputMixedDesc.sourceMap g).hom.toFunctor ≅
    (InputNormalizationPrism.firstSource (projection.app Y) ≫
      BoundedFlatPerfectNativeSquareFiveSimplex.source (laurent.map g) (k.app Y)).hom.toFunctor :=
  (InputChartSquareParameter.nodes g k hk 1).2

/-- All five attached chart nodes are one complete precomposed original raw square family. -/
theorem chart_nodes (i : Fin 5) :
    InputChartSquareParameter.nodes g k hk (normalizationRow i) =
      preReferenceNode (InputMixedDesc.sourceMap g)
        (InputNormalizationPrism.firstSource (projection.app Y)) (chartAnchor g k hk)
        (BoundedFlatPerfectNativeSquareFiveSimplex.nodes
          (laurent.map g) (k.app Y) (k.app X) (polynomial.map g) (k.naturality g) i) := by
  unfold InputChartSquareParameter.nodes
  rw [commuting_normalization_nodes]
  exact ModelSimplex.pre_pre_node (InputMixedDesc.sourceMap g)
    (boundedAboveFlatGlobalSectionModelFunctor.map (projection.app Y).op)
      (evaluationModel (op (polynomial.obj Y)))
    (BoundedFlatPerfectNativeSquareFiveSimplex.source (laurent.map g) (k.app Y))
      (evaluationComparisonIso (laurent.map g ≫ k.app Y))
    (InputChartSquareParameter.sourceIso g k hk) (BoundedFlatPerfectNativeSquareFiveSimplex.nodes
          (laurent.map g) (k.app Y) (k.app X) (polynomial.map g) (k.naturality g) i)

private theorem pre_identity_anchor
    {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} (F : V ⟶ T)
    (J : V ⟶ W) (H : W ⟶ T) (ρ : F.hom.toFunctor ≅ (J ≫ H).hom.toFunctor)
    (N : Σ G : W ⟶ T, H.hom.toFunctor ≅ G.hom.toFunctor) :
    preReferenceNode F J (ρ ≪≫ isoWhiskerRight (Iso.refl J.hom.toFunctor) H.hom.toFunctor) N =
      preReferenceNode F J ρ N := by
  rw [isoWhiskerRight_refl]
  exact congrArg (fun σ ↦ preReferenceNode F J σ N) (Iso.trans_refl ρ)

/-- The initial product row uses the same five original raw normalization nodes. -/
theorem product_nodes (i : Fin 5) :
    InputRawChartProductNodes.nodes g k hk (SimplexGrid.index 1 4 (0, i)) =
      preReferenceNode (InputMixedDesc.sourceMap g)
        (InputNormalizationPrism.firstSource (projection.app Y))
        (InputRawChartProductNodes.anchor g k hk) (InputRawChartRows.squareNodes g k i) := by
  have h := CommonReferenceProduct.product_row_nodes (InputMixedDesc.sourceMap g)
    (InputNormalizationPrism.firstSource (projection.app Y))
    (InputNormalizationPrism.firstVertices (projection.app Y))
    (InputNormalizationPrism.firstAnchors (projection.app Y)) (InputRawChartRows.squareSource g k)
    (InputRawSquareProduct.squareVertices (laurent.map g) (k.app Y)
      (k.app X) (polynomial.map g) (k.naturality g))
    (InputRawSquareProduct.squareAnchors (laurent.map g) (k.app Y)
      (k.app X) (polynomial.map g) (k.naturality g)) (InputRawChartProductNodes.anchor g k hk) 0 i
  change InputRawChartProductNodes.nodes g k hk (SimplexGrid.index 1 4 (0, i)) =
    preReferenceNode (InputMixedDesc.sourceMap g)
      (InputNormalizationPrism.firstSource (projection.app Y))
      (InputRawChartProductNodes.anchor g k hk ≪≫
        isoWhiskerRight (Iso.refl _) (InputRawChartRows.squareSource g k).hom.toFunctor)
      (InputRawChartRows.squareNodes g k i) at h
  exact h.trans (pre_identity_anchor (InputMixedDesc.sourceMap g)
    (InputNormalizationPrism.firstSource (projection.app Y)) (InputRawChartRows.squareSource g k)
    (InputRawChartProductNodes.anchor g k hk) (InputRawChartRows.squareNodes g k i))

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartNormalizationNodes
