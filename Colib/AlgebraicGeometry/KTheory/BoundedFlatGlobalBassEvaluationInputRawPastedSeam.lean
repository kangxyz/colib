/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputRawPastedParameter
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartRawFace
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartParameters
public import Colib.Topology.Path.ScalarPathCells

/-!
# The original middle quarter of the raw input source seam

The two original normalization paths meet in the selected source word of raw descent.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity Topology
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputRawPastedSeam
open GlobalSectionChangeIndex InputRawChartRows InputNormalizationPrism Path.CarrierHalfPaths
open BoundedFlatPerfectProjectionRectangleParameters
open BoundedFlatCoefficientBassH0Diagram (plusFace minusFace)

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- The terminal source-column node is the full original postcomposed chart target. -/
theorem column_terminal_node :
    InputRawChartProductNodes.nodes g k hk (SimplexGrid.index 1 4 (1, 2)) =
      InputChartReference.postNode g k hk 4 :=
  (InputRawChartProductNodes.terminal_nodes g k hk 2).trans
    ((InputRawChartRows.chart_nodes g k hk 2).symm.trans
      ((InputRawDesc.chart_node g k hk 11).symm.trans
        (InputChartReference.post_target_node g k hk).symm))

private theorem pair_iso_other {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
  {F₀ F₁ : V ⟶ W} {G₀ G₁ : W ⟶ T}
    (e : F₀.hom.toFunctor ≅ F₁.hom.toFunctor) (d : G₀.hom.toFunctor ≅ G₁.hom.toFunctor) :
    (Functor.uncurry.obj (whiskeringLeft V.obj.Obj W.obj.Obj T.obj.Obj)).mapIso (e.prod d) =
      isoWhiskerLeft F₀.hom.toFunctor d ≪≫ isoWhiskerRight e G₁.hom.toFunctor := by
  apply Iso.ext
  ext A
  exact d.hom.naturality (e.hom.app A)

attribute [local irreducible] InputRawChartProductNodes.anchor
  InputRawChartProductNodes.terminalAnchor InputChartReference.chartSourceIso
  evaluationComparisonIso evaluationCompositionFirstIso evaluationCompositionTargetIso

private def columnAnchor (i : Fin 2) :
    (InputMixedDesc.sourceMap g).hom.toFunctor ≅
      (firstVertices (projection.app Y) i ≫
        BoundedFlatPerfectBinarySimplex.targetMap (laurent.map g) (k.app Y)).hom.toFunctor :=
  InputRawChartProductNodes.anchor g k hk ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((firstAnchors (projection.app Y) i).prod
        (BoundedFlatPerfectBinarySimplex.total (laurent.map g) (k.app Y)))

private def columnNode (i : Fin 2) : InputChartReference.Node g :=
  ⟨firstVertices (projection.app Y) i ≫
      BoundedFlatPerfectBinarySimplex.targetMap (laurent.map g) (k.app Y), columnAnchor g k hk i⟩

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
      (Functor.uncurry.obj (whiskeringLeft V.obj.Obj W.obj.Obj T.obj.Obj)).mapIso
        ((ρ i).prod (eta j))⟩ := by
  unfold CommonReferenceProduct.vertices CommonReferenceProduct.references
  rw [SimplexGrid.decode_index]

private theorem product_column_node (i : Fin 2) :
    InputRawChartProductNodes.nodes g k hk (SimplexGrid.index 1 4 (i, 2)) =
      columnNode g k hk i := by
  unfold InputRawChartProductNodes.nodes
  rw [product_node_index]
  rfl

private theorem product_column_reference
  {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    {F₀ F₁ : V ⟶ W} {G₀ G₁ : W ⟶ T} {R : V ⟶ T}
    (a : R.hom.toFunctor ≅ (F₀ ≫ G₀).hom.toFunctor)
    (e : F₀.hom.toFunctor ≅ F₁.hom.toFunctor) (d : G₀.hom.toFunctor ≅ G₁.hom.toFunctor) :
    (a ≪≫ (Functor.uncurry.obj (whiskeringLeft V.obj.Obj W.obj.Obj T.obj.Obj)).mapIso
      ((Iso.refl F₀.hom.toFunctor).prod d)) ≪≫ isoWhiskerRight e G₁.hom.toFunctor =
    a ≪≫
      (Functor.uncurry.obj (whiskeringLeft V.obj.Obj W.obj.Obj T.obj.Obj)).mapIso (e.prod d) := by
  rw [pair_iso_other, pair_iso_other]
  simp only [isoWhiskerRight_refl, Iso.trans_refl, Iso.trans_assoc]

private theorem node_anchor_congr {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
  {R : V ⟶ W}
    {N M : CommonReferenceNerve.Node R} (e : N = M)
    (h : N.1.hom.toFunctor = M.1.hom.toFunctor) : N.2 ≪≫ eqToIso h = M.2 := by
  cases e
  simp

set_option backward.isDefEq.respectTransparency true in
private theorem product_column_anchor :
    columnAnchor g k hk 0 ≪≫
      isoWhiskerRight (evaluationComparisonIso (projection.app Y))
        (BoundedFlatPerfectBinarySimplex.targetMap (laurent.map g) (k.app Y)).hom.toFunctor =
    columnAnchor g k hk 1 := by
  dsimp only [columnAnchor, firstAnchors, Fin.cases_zero, Fin.cases_succ]
  exact product_column_reference (R := InputMixedDesc.sourceMap g)
    (F₀ := firstSource (projection.app Y)) (F₁ := firstTarget (projection.app Y))
    (G₀ := squareSource g k)
    (G₁ := BoundedFlatPerfectBinarySimplex.targetMap (laurent.map g) (k.app Y))
    (InputRawChartProductNodes.anchor g k hk)
    (evaluationComparisonIso (projection.app Y))
    (BoundedFlatPerfectBinarySimplex.total (laurent.map g) (k.app Y))

private theorem whisker_pasting {A B C : Type*} [Category A] [Category B] [Category C]
    (J : B ⥤ C) {R S : A ⥤ C} {F G H : A ⥤ B}
    (a : R ⟶ S) (b : S ⟶ F ⋙ J) (e : F ⟶ G) (d : G ⟶ H) (h : F ⟶ H)
    (he : e ≫ d = h) :
    (a ≫ (b ≫ whiskerRight e J)) ≫ whiskerRight d J =
      a ≫ (b ≫ whiskerRight h J) := by
  rw [Category.assoc, Category.assoc, ← whiskerRight_comp, he]

private theorem post_column_anchor :
    (InputChartReference.postNode g k hk 3).2 ≪≫
      isoWhiskerRight (evaluationComparisonIso (projection.app Y))
        (BoundedFlatPerfectBinarySimplex.targetMap (laurent.map g) (k.app Y)).hom.toFunctor =
    (InputChartReference.postNode g k hk 4).2 := by
  apply Iso.ext
  change ((InputChartReference.chartSourceIso g k hk).hom ≫
    ((evaluationCompositionFirstIso (laurent.map g) (k.app Y ≫ projection.app Y)).hom ≫
      whiskerRight (evaluationCompositionFirstIso (k.app Y) (projection.app Y)).hom
        (evaluationRawMap (laurent.map g)).hom.toFunctor)) ≫
    whiskerRight (evaluationCompositionSecondIso (k.app Y) (projection.app Y)).hom
      (evaluationRawMap (laurent.map g)).hom.toFunctor =
    (InputChartReference.chartSourceIso g k hk).hom ≫
      ((evaluationCompositionFirstIso (laurent.map g) (k.app Y ≫ projection.app Y)).hom ≫
        whiskerRight ((evaluationComparisonIso (k.app Y ≫ projection.app Y)).hom ≫
          (evaluationCompositionTargetIso (k.app Y) (projection.app Y)).hom)
          (evaluationRawMap (laurent.map g)).hom.toFunctor)
  exact whisker_pasting (evaluationRawMap (laurent.map g)).hom.toFunctor
    (InputChartReference.chartSourceIso g k hk).hom
    (evaluationCompositionFirstIso (laurent.map g) (k.app Y ≫ projection.app Y)).hom
    (evaluationCompositionFirstIso (k.app Y) (projection.app Y)).hom
    (evaluationCompositionSecondIso (k.app Y) (projection.app Y)).hom
    ((evaluationComparisonIso (k.app Y ≫ projection.app Y)).hom ≫
      (evaluationCompositionTargetIso (k.app Y) (projection.app Y)).hom)
    (evaluationComposition_pasting (k.app Y) (projection.app Y)).symm

private theorem cancel_column {C : Type*} [Category C] {R A B : C}
    (a₀ b₀ : R ≅ A) (a₁ b₁ : R ≅ B) (e : A ≅ B)
    (hp : a₀ ≪≫ e = a₁) (hq : b₀ ≪≫ e = b₁)
    (h : B = B) (ht : a₁ ≪≫ eqToIso h = b₁) :
    a₀.hom ≫ eqToHom (rfl : A = A) = b₀.hom := by
  rw [eqToHom_refl, Category.comp_id]
  have hh : a₁ = b₁ := by
    simpa only [eqToIso_refl, Iso.trans_refl] using ht
  apply (Iso.cancel_iso_hom_right _ _ e).mp
  exact (congrArg Iso.hom hp).trans
    ((congrArg Iso.hom hh).trans (congrArg Iso.hom hq).symm)

set_option backward.isDefEq.respectTransparency true in
/-- The initial source-column node retains the complete original evaluation-cut anchor. -/
theorem column_initial_node :
    InputRawChartProductNodes.nodes g k hk (SimplexGrid.index 1 4 (0, 2)) =
      InputChartReference.postNode g k hk 3 := by
  rw [product_column_node]
  apply ModelSimplex.reference_node_eq (by rfl)
  have he := (product_column_node g k hk 1).symm.trans (column_terminal_node g k hk)
  have hf := congrArg (fun N : InputChartReference.Node g => N.1.hom.toFunctor) he
  exact cancel_column (columnAnchor g k hk 0) (InputChartReference.postNode g k hk 3).2
    (columnAnchor g k hk 1) (InputChartReference.postNode g k hk 4).2
    (isoWhiskerRight (evaluationComparisonIso (projection.app Y))
      (BoundedFlatPerfectBinarySimplex.targetMap (laurent.map g) (k.app Y)).hom.toFunctor)
    (product_column_anchor g k hk) (post_column_anchor g k hk) hf
    (node_anchor_congr he hf)

/-- Both dependent nodes of the moving projection column are the actual chart cut and target. -/
theorem column_nodes (i : Fin 2) :
    InputRawChartProductNodes.nodes g k hk
      ((SimplexGrid.columnFace 1 4 2).toOrderHom i) =
    InputChartReference.postNode g k hk
      ((SimplexCategory.Hom.mk ⟨![3, 4], by decide⟩ : ⦋1⦌ ⟶ ⦋4⦌).toOrderHom i) := by
  fin_cases i
  · exact column_initial_node g k hk
  · exact column_terminal_node g k hk

private theorem map_edge_scalar {p q : ℕ} (α : ⦋p⦌ ⟶ ⦋q⦌)
    (i j : Fin (p + 1)) (t : unitInterval) :
    StdSimplex.map α.toOrderHom ((edge i j) t) =
      edge (α.toOrderHom i) (α.toOrderHom j) t := map_edge α i j t

/-- Every point of the original evaluation column retains its two complete attached nodes. -/
theorem column_parameter (t : unitInterval) :
    InputRawChartProductNodes.parameter g k hk (t, 0) =
      CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
        (InputChartReference.postNode g k hk) ((edge 3 4) t) := by
  change CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
    (InputRawChartProductNodes.nodes g k hk) (InputRawSquareProduct.parameter (t, 0)) = _
  rw [InputRawSquareProduct.parameter_square_zero]
  have h := CommonReferenceNerve.parameter_eq_of_face_nodes (InputMixedDesc.sourceMap g)
    (InputChartReference.postNode g k hk) (InputRawChartProductNodes.nodes g k hk)
    (SimplexCategory.Hom.mk ⟨![3, 4], by decide⟩ : ⦋1⦌ ⟶ ⦋4⦌)
    (SimplexGrid.columnFace 1 4 2) (column_nodes g k hk) ((edge (k := 1) 0 1) t)
  exact h.trans (congrArg
    (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputChartReference.postNode g k hk))
    (map_edge_scalar (SimplexCategory.Hom.mk ⟨![3, 4], by decide⟩ : ⦋1⦌ ⟶ ⦋4⦌) 0 1 t))

private theorem map_binary_scalar {p q : ℕ} (α : ⦋p⦌ ⟶ ⦋q⦌)
    (i j m : Fin (p + 1)) (t : unitInterval) :
    StdSimplex.map α.toOrderHom ((binaryPath i j m) t) =
      binaryPath (α.toOrderHom i) (α.toOrderHom j) (α.toOrderHom m) t :=
  map_binaryPath α i j m t

/-- The original postcomposed binary normalization is the complete raw source-chart path. -/
theorem normalization_parameter (t : unitInterval) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputChartReference.postNode g k hk) ((binaryPath 1 2 4) t) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputChartReference.rawNode g k hk) ((binaryPath 2 3 11) t) := by
  have h := InputChartReference.normalization_parameter g k hk ((binaryPath 0 1 2) t)
  rw [map_binary_scalar, map_binary_scalar] at h
  exact h

/-- The postcomposition of the exact original eight-node characteristic map. -/
def postCharacteristic :=
  (CommonReferenceNerve.mapParameter (InputMixedDesc.postNode g)).comp
    (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap Y) (InputChartSimplex.nodes Y))

/-- The actual collapsed boundary retains the original right-associated three-piece word. -/
def postPath : Path (StdSimplex.single 3 : StdSimplex ℝ (Fin 8)) (StdSimplex.single 6) :=
  (edge 3 4).trans (((binaryPath 1 2 4).symm.trans (binaryPath 1 5 7)).trans (edge 6 7).symm)

/-- The actual `toSquare` face restricts to the unchanged original target path. -/
theorem post_square_one (s : unitInterval) :
    InputMixedDesc.postSquareParameter g (1, s) = postCharacteristic g (postPath s) := by
  change postCharacteristic g (collapsed InputChartSimplex.descParameter (1, s)) = _
  exact congrArg (postCharacteristic g)
    (collapsed_top_path InputChartSimplex.descParameter s)

/-- The positive first half is the full moving-input column at raw-square source time. -/
theorem plus_parameter (t : unitInterval) :
    postCharacteristic g ((edge 3 4) t) =
      InputRawChartProductNodes.parameter g plus GlobalRawBass.plus_projection (t, 0) := by
  rw [column_parameter]
  have h := InputChartReference.plus_post_parameter g ((edge 3 4) t)
  rw [map_edge_scalar] at h
  exact h.symm

/-- The inverse final quarter retains the separate original moving-input column. -/
theorem minus_parameter (t : unitInterval) :
    postCharacteristic g ((edge 6 7) t) =
      InputRawChartProductNodes.parameter g minus GlobalRawBass.minus_projection (t, 0) := by
  rw [column_parameter]
  have h := InputChartReference.minus_post_parameter g ((edge 3 4) t)
  rw [map_edge_scalar] at h
  exact h.symm

/-- The positive raw normalization path is the corresponding postcomposed chart face. -/
theorem plus_normalization_parameter (t : unitInterval) :
    postCharacteristic g ((binaryPath 1 2 4) t) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputRawDesc.nodes g)
      (D plusFace t) := by
  have hp := InputChartReference.plus_post_parameter g ((binaryPath 1 2 4) t)
  rw [map_binary_scalar] at hp
  have hr := InputRawDesc.plus_chart_characteristic g ((binaryPath 2 3 11) t)
  rw [map_binary_scalar] at hr
  exact hp.symm.trans ((normalization_parameter g plus GlobalRawBass.plus_projection t).trans
    hr.symm)

/-- The inverse raw normalization path retains its original chart clock. -/
theorem minus_normalization_parameter (t : unitInterval) :
    postCharacteristic g ((binaryPath 1 5 7) t) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputRawDesc.nodes g)
      (D minusFace t) := by
  have hp := InputChartReference.minus_post_parameter g ((binaryPath 1 2 4) t)
  rw [map_binary_scalar] at hp
  have hr := InputRawDesc.minus_chart_characteristic g ((binaryPath 2 3 11) t)
  rw [map_binary_scalar] at hr
  exact hp.symm.trans ((normalization_parameter g minus GlobalRawBass.minus_projection t).trans
    hr.symm)

/-- The whole middle quarter is the original raw descent source word, with its own half clock. -/
theorem middle_parameter (t : unitInterval) :
    postCharacteristic g (((binaryPath 1 2 4).symm.trans (binaryPath 1 5 7)) t) =
      InputRawDesc.parameter g (0, t) := by
  rw [InputRawDesc.parameter_zero_word]
  rw [Path.trans_apply, Path.trans_apply]
  split
  · exact plus_normalization_parameter g _
  · exact minus_normalization_parameter g _

/-- The entire common-reference seam agrees at every original height, including both joins. -/
theorem seam (s : unitInterval) :
    InputMixedDesc.postSquareParameter g (1, s) = InputRawPastedParameter.parameter g (0, s) := by
  rw [post_square_one]
  rcases three_cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [InputRawPastedParameter.parameter_lower]
    rw [postPath, path_lower]
    exact plus_parameter g t
  · rw [InputRawPastedParameter.parameter_middle]
    rw [postPath, path_upper, path_lower]
    exact middle_parameter g t
  · rw [InputRawPastedParameter.parameter_upper]
    rw [postPath, path_upper, path_upper]
    exact minus_parameter g (unitInterval.symm t)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputRawPastedSeam
