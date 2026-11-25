/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityUnitBoundaryNodes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1FirstPolynomialRow
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1SecondPolynomialRow
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassUnitChartSideRows
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectProjectionRightRows
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitUnitRows
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceProductColumns

/-!
# Actual initial-surface boundary nodes for the global raw identity carrier

The full global thirty-one-node input surface is attached to the actual unit-side, polynomial-top,
projection-by-Laurent-unit, and base-unit-by-projection node families. Every equality retains
both the model morphism and its complete reference transformation.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Topology
open CategoryTheory.Waldhausen SmallWaldhausenCategory
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityBoundaryNodes
open BoundedFlatPerfectOriginalUnitSquareSimplex BoundedFlatCoefficientBassUnitHZeroNodes
open BoundedFlatCoefficientBassH1Join (nativeMiddleReference native_middle_column
  native_last_column)
open BoundedFlatPerfectProjectionBinaryRows BoundedFlatPerfectNativeMergedRows
open ModelSimplex CommonReferenceProduct
local notation "WC" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "source" => InputIdentityNodes.source
open InputIdentityTopNodes
open InputIdentityUnitBoundaryNodes (bottomNodes bottomSourceIso
  plusSideNodes minusSideNodes plus_total_anchor minus_total_anchor plus_side_actual
  minus_side_actual plus_bottom_first minus_bottom_first)

private theorem post_identity_anchor {V W T : WideSubcategory preservesZero.{u}} (F : V ⟶ T)
    (H : V ⟶ W) (J : W ⟶ T) (ρ : F.hom.toFunctor ≅ (H ≫ J).hom.toFunctor)
    (N : Σ G : V ⟶ W, H.hom.toFunctor ≅ G.hom.toFunctor) :
    postReferenceNode F J (ρ ≪≫ isoWhiskerLeft H.hom.toFunctor (Iso.refl J.hom.toFunctor)) N =
      postReferenceNode F J ρ N := by
  rw [isoWhiskerLeft_refl]
  exact congrArg (fun σ ↦ postReferenceNode F J σ N) (Iso.trans_refl ρ)

private theorem pre_identity_anchor {V W T : WideSubcategory preservesZero.{u}} (F : V ⟶ T)
    (J : V ⟶ W) (H : W ⟶ T) (ρ : F.hom.toFunctor ≅ (J ≫ H).hom.toFunctor)
    (N : Σ G : W ⟶ T, H.hom.toFunctor ≅ G.hom.toFunctor) :
    preReferenceNode F J (ρ ≪≫ isoWhiskerRight (Iso.refl J.hom.toFunctor) H.hom.toFunctor) N =
      preReferenceNode F J ρ N := by
  rw [isoWhiskerRight_refl]
  exact congrArg (fun σ ↦ preReferenceNode F J σ N) (Iso.trans_refl ρ)

private theorem post_anchor_node {V W T' : WideSubcategory preservesZero.{u}} (F : V ⟶ T')
    (J : W ⟶ T') {H L : V ⟶ W} (ρ : F.hom.toFunctor ≅ (H ≫ J).hom.toFunctor)
    (η : H.hom.toFunctor ≅ L.hom.toFunctor)
    (N : Σ G : V ⟶ W, L.hom.toFunctor ≅ G.hom.toFunctor) :
    postReferenceNode F J ρ (reanchorNode η N) =
      postReferenceNode F J (ρ ≪≫ isoWhiskerRight η J.hom.toFunctor) N := by
  rcases N with ⟨G, σ⟩
  apply congrArg (fun ν : F.hom.toFunctor ≅ (G ≫ J).hom.toFunctor ↦
    (⟨G ≫ J, ν⟩ : Σ J' : V ⟶ T', F.hom.toFunctor ≅ J'.hom.toFunctor))
  change ρ ≪≫ isoWhiskerRight (η ≪≫ σ) J.hom.toFunctor = _
  rw [isoWhiskerRight_trans, Iso.trans_assoc]

private theorem anchor_post_node {V W T' : WideSubcategory preservesZero.{u}}
    {F K : V ⟶ T'} (J : W ⟶ T') {H : V ⟶ W}
    (η : F.hom.toFunctor ≅ K.hom.toFunctor)
    (ρ : K.hom.toFunctor ≅ (H ≫ J).hom.toFunctor)
    (N : Σ G : V ⟶ W, H.hom.toFunctor ≅ G.hom.toFunctor) :
    reanchorNode η (postReferenceNode K J ρ N) =
      postReferenceNode F J (η ≪≫ ρ) N := by
  rcases N with ⟨G, σ⟩
  exact congrArg (fun ν : F.hom.toFunctor ≅ (G ≫ J).hom.toFunctor ↦
    (⟨G ≫ J, ν⟩ : CommonReferenceNerve.Node F))
    (Iso.trans_assoc η ρ (isoWhiskerRight σ J.hom.toFunctor)).symm

private theorem postReferenceNode_source {V W T' : WideSubcategory preservesZero.{u}}
    (F : V ⟶ T') (J : W ⟶ T') {H : V ⟶ W}
    (ρ : F.hom.toFunctor ≅ (H ≫ J).hom.toFunctor) :
    postReferenceNode F J ρ ⟨H, Iso.refl _⟩ = ⟨H ≫ J, ρ⟩ := by
  have h : isoWhiskerRight (Iso.refl H.hom.toFunctor) J.hom.toFunctor =
      Iso.refl (H.hom.toFunctor ⋙ J.hom.toFunctor) := by
    rw [isoWhiskerRight_refl]
  exact congrArg (fun ν : F.hom.toFunctor ≅ (H ≫ J).hom.toFunctor ↦
    (⟨H ≫ J, ν⟩ : CommonReferenceNerve.Node F))
    ((congrArg (fun τ ↦ ρ ≪≫ τ) h).trans (Iso.trans_refl ρ))

section Rectangle

variable {A B' C : Scheme.{u}} (p : B' ⟶ A) (q : C ⟶ B')
  (F : asSmallCategory (WC A) ⟶ asSmallCategory (WC C))
  (δ : F.hom.toFunctor ≅ (BoundedFlatPerfectBinarySimplex.sourceMap q p).hom.toFunctor)

/-- The original polynomial unit vertices with the unchanged Laurent postcomposition. -/
private def rectangleTopNodes (i : Fin 8) :
    Σ G : asSmallCategory (WC A) ⟶
      asSmallCategory (WC C), F.hom.toFunctor ≅ G.hom.toFunctor :=
  postReferenceNode F (sourceMap q) (δ ≪≫ BoundedFlatPerfectBinarySimplex.total q p)
    ⟨vertices p i, references p i⟩

/-- The reference isomorphism to the postcomposed middle binary column. -/
private def middleColumnAnchor : F.hom.toFunctor ≅
    (BoundedFlatPerfectBinarySimplex.sourceMap (𝟙 B') p ≫ sourceMap q).hom.toFunctor :=
  (δ ≪≫ eqToIso (rectangleSourceEq p q)) ≪≫
    (nativeMiddleReference p q q (𝟙 B') (𝟙 C) (by simp) (q ≫ p) rfl ≪≫
      BoundedFlatPerfectBinarySimplex.total q ((𝟙 B') ≫ p))

/-- The reference isomorphism to the postcomposed last binary column. -/
private def lastColumnAnchor : F.hom.toFunctor ≅
    (BoundedFlatPerfectBinarySimplex.sourceMap p (𝟙 A) ≫ sourceMap q).hom.toFunctor :=
  (δ ≪≫ eqToIso (rectangleSourceEq p q)) ≪≫
    (nativeLastReference p q p q (𝟙 A) (𝟙 B') (𝟙 C) (by simp) (by simp) (q ≫ p) rfl ≪≫
      BoundedFlatPerfectBinarySimplex.total q (p ≫ (𝟙 A)))

/-- The first H0 polynomial column retains the actual binary normalization postmap. -/
private theorem rectangle_middle_column_form (i : Fin 3) :
    rectangleNodes p q F δ (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom
      (leftIndex i)) =
      postReferenceNode F (sourceMap q) (middleColumnAnchor p q F δ)
        (binaryNodes (𝟙 B') p i) := by
  unfold rectangleNodes
  rw [native_middle_column]
  exact anchor_post_node _ _ _ _

/-- The second column retains its separate original total-square reference transport. -/
private theorem rectangle_last_column_form (i : Fin 3) :
    rectangleNodes p q F δ (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom
      (leftIndex i)) =
      postReferenceNode F (sourceMap q) (lastColumnAnchor p q F δ)
        (binaryNodes p (𝟙 A) i) := by
  unfold rectangleNodes
  rw [native_last_column]
  exact anchor_post_node _ _ _ _

/-- The top's first row is precisely the original polynomial binary normalization. -/
private theorem rectangle_top_right_form (i : Fin 3) :
    rectangleTopNodes p q F δ (![0, 1, 2] i) =
      postReferenceNode F (sourceMap q)
        ((δ ≪≫ BoundedFlatPerfectBinarySimplex.total q p) ≪≫
          isoWhiskerRight (eqToIso (rightBinarySourceEq p)) (sourceMap q).hom.toFunctor)
        (binaryNodes (𝟙 B') p i) := by
  unfold rectangleTopNodes
  rw [unit_right_row]
  exact post_anchor_node _ _ _ _ _

/-- The other top row retains the original left unit source equality. -/
private theorem rectangle_top_left_form (i : Fin 3) :
    rectangleTopNodes p q F δ (![0, 4, 5] i) =
      postReferenceNode F (sourceMap q)
        ((δ ≪≫ BoundedFlatPerfectBinarySimplex.total q p) ≪≫
          isoWhiskerRight (eqToIso (leftBinarySourceEq p)) (sourceMap q).hom.toFunctor)
        (binaryNodes p (𝟙 A) i) := by
  unfold rectangleTopNodes
  rw [unit_left_row]
  exact post_anchor_node _ _ _ _ _

/-- All three first-column nodes follow from the full common source and original binary data. -/
private theorem rectangle_top_right (i : Fin 3) :
    rectangleNodes p q F δ (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom
      (leftIndex i)) =
      rectangleTopNodes p q F δ (![0, 1, 2] i) := by
  apply post_families_match F (sourceMap q) (BoundedFlatPerfectBinarySimplex.sourceMap (𝟙 B') p)
    (binaryNodes (𝟙 B') p) (rectangle_middle_column_form p q F δ)
      (rectangle_top_right_form p q F δ) 0 ?_ i
  change rectangleNodes p q F δ 5 =
    postReferenceNode F (sourceMap q) (δ ≪≫ BoundedFlatPerfectBinarySimplex.total q p)
      ⟨sourceMap p, Iso.refl _⟩
  exact (rectangle_middle_source p q F δ).trans
    (postReferenceNode_source F (sourceMap q) (H := sourceMap p)
      (δ ≪≫ BoundedFlatPerfectBinarySimplex.total q p)).symm

/-- The original last column shares its complete source, not merely its realized endpoint. -/
private theorem rectangle_top_left (i : Fin 3) :
    rectangleNodes p q F δ (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom
      (leftIndex i)) =
      rectangleTopNodes p q F δ (![0, 4, 5] i) := by
  apply post_families_match F (sourceMap q) (BoundedFlatPerfectBinarySimplex.sourceMap p (𝟙 A))
    (binaryNodes p (𝟙 A)) (rectangle_last_column_form p q F δ)
      (rectangle_top_left_form p q F δ) 0 ?_ i
  change rectangleNodes p q F δ 5 =
    postReferenceNode F (sourceMap q) (δ ≪≫ BoundedFlatPerfectBinarySimplex.total q p)
      ⟨sourceMap p, Iso.refl _⟩
  exact (rectangle_middle_source p q F δ).trans
    (postReferenceNode_source F (sourceMap q) (H := sourceMap p)
      (δ ≪≫ BoundedFlatPerfectBinarySimplex.total q p)).symm

/-- The reference isomorphism to the first normalized triple composite. -/
private def firstTripleAnchor : F.hom.toFunctor ≅ (BoundedFlatPerfectTripleSimplex.source
  (𝟙 C) q p).hom.toFunctor :=
  (δ ≪≫ eqToIso (rectangleSourceEq p q)) ≪≫
    eqToIso (BoundedFlatPerfectProjectionReference.anchor p q (𝟙 C) (q ≫ p) rfl)

/-- The reference isomorphism to the last normalized triple composite. -/
private def lastTripleAnchor : F.hom.toFunctor ≅ (BoundedFlatPerfectTripleSimplex.source q p
  (𝟙 A)).hom.toFunctor :=
  (δ ≪≫ eqToIso (rectangleSourceEq p q)) ≪≫
    nativeLastReference p q p q (𝟙 A) (𝟙 B') (𝟙 C) (by simp) (by simp) (q ≫ p) rfl

/-- Every original first-triple node retains its complete equality and reference transport. -/
private theorem rectangle_first_triple (i : Fin 8) :
    rectangleNodes p q F δ (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom i) =
      ⟨BoundedFlatPerfectSplitTripleSimplex.vertices (𝟙 C) q p i,
        firstTripleAnchor p q F δ ≪≫
          BoundedFlatPerfectSplitTripleSimplex.references (𝟙 C) q p i⟩ := by
  have h := congrArg (reanchorNode δ)
    (projection_first_nodes p q p q (𝟙 A) (𝟙 B') (𝟙 C) (by simp) (by simp)
      (q ≫ p) rfl (BoundedFlatPerfectBinarySimplex.sourceMap q p) (rectangleSourceEq p q) i)
  simpa only [rectangleNodes, projectionNativeNode, ModelSimplex.reanchorNodes, reanchorNode,
    projectionFirstReference, firstTripleAnchor, Iso.trans_assoc] using h

/-- Every last-triple node keeps the actual total-square transport before its transformations. -/
private theorem rectangle_last_triple (i : Fin 8) :
    rectangleNodes p q F δ (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom i) =
      ⟨BoundedFlatPerfectSplitTripleSimplex.vertices q p (𝟙 A) i,
        lastTripleAnchor p q F δ ≪≫
          BoundedFlatPerfectSplitTripleSimplex.references q p (𝟙 A) i⟩ := by
  have h := congrArg (reanchorNode (δ ≪≫ eqToIso (rectangleSourceEq p q)))
    (native_last_nodes p q p q (𝟙 A) (𝟙 B') (𝟙 C) (by simp) (by simp) (q ≫ p) rfl i)
  simpa only [rectangleNodes, reanchorNode, lastTripleAnchor, Iso.trans_assoc] using h

/-- The first-triple reference followed by its source-column normalization. -/
private def sourceColumnAnchor : F.hom.toFunctor ≅
    (BoundedFlatPerfectBinarySimplex.sourceMap q p ≫ sourceMap (𝟙 C)).hom.toFunctor :=
  firstTripleAnchor p q F δ ≪≫ BoundedFlatPerfectBinarySimplex.total (𝟙 C) (q ≫ p)

/-- The target-row reference induced by the last-triple reference. -/
private def targetRowAnchor : F.hom.toFunctor ≅
    (sourceMap (𝟙 A) ≫ BoundedFlatPerfectBinarySimplex.sourceMap q p).hom.toFunctor :=
  rightRowReference F q p (𝟙 A) (lastTripleAnchor p q F δ)

/-- The entire original source projection path is a fixed postcomposed binary column. -/
private theorem rectangle_source_column_form (i : Fin 3) :
    rectangleNodes p q F δ (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom
      (leftIndex i)) =
      postReferenceNode F (sourceMap (𝟙 C)) (sourceColumnAnchor p q F δ)
        (binaryNodes q p i) :=
  (rectangle_first_triple p q F δ (leftIndex i)).trans
    (triple_left_column_iso F (𝟙 C) q p (firstTripleAnchor p q F δ) i)

/-- The entire original target projection path is a fixed precomposed binary row. -/
private theorem rectangle_target_row_form (i : Fin 3) :
    rectangleNodes p q F δ (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom
      (rightIndex i)) =
      preReferenceNode F (sourceMap (𝟙 A)) (targetRowAnchor p q F δ)
        (binaryNodes q p i) :=
  (rectangle_last_triple p q F δ (rightIndex i)).trans
    (triple_right_row F q p (𝟙 A) (lastTripleAnchor p q F δ) i)

end Rectangle

variable (X : Scheme.{u})

/-- Both original lower positive chart rows retain all their actual reference nodes. -/
theorem plus_side_right (i : Fin 3) :
    InputIdentityNodes.chartNodes X plus plus_projection
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
      plusSideNodes X (![0, 1, 2] i) :=
  (InputIdentityNodes.chart_unit_right X plus plus_projection i).trans
    (plus_side_actual X (![0, 1, 2] i)).symm

theorem plus_side_left (i : Fin 3) :
    InputIdentityNodes.chartNodes X plus plus_projection
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
      plusSideNodes X (![0, 4, 5] i) :=
  (InputIdentityNodes.chart_unit_left X plus plus_projection i).trans
    (plus_side_actual X (![0, 4, 5] i)).symm

/-- The inverse chart retains its own two original binary rows and their full references. -/
theorem minus_side_right (i : Fin 3) :
    InputIdentityNodes.chartNodes X minus minus_projection
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
      minusSideNodes X (![0, 1, 2] i) :=
  (InputIdentityNodes.chart_unit_right X minus minus_projection i).trans
    (minus_side_actual X (![0, 1, 2] i)).symm

theorem minus_side_left (i : Fin 3) :
    InputIdentityNodes.chartNodes X minus minus_projection
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
      minusSideNodes X (![0, 4, 5] i) :=
  (InputIdentityNodes.chart_unit_left X minus minus_projection i).trans
    (minus_side_actual X (![0, 4, 5] i)).symm

/-- The positive polynomial columns use the exact original top-square nodes. -/
theorem plus_top_right (i : Fin 3) :
    InputIdentityNodes.chartNodes X plus plus_projection
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) =
      plusNodes X (![0, 1, 2] i) := by
  exact (InputIdentityNodes.chart_identity X plus plus_projection _).trans
    ((rectangle_top_right _ _ _ _ i).trans
      (congrArg (fun ρ ↦ postReferenceNode (source X) (sourceMap (plus.app X))
        ρ ⟨vertices (projection.app X) (![0, 1, 2] i),
          references (projection.app X) (![0, 1, 2] i)⟩)
        (plus_total_anchor X)))

theorem plus_top_left (i : Fin 3) :
    InputIdentityNodes.chartNodes X plus plus_projection
      (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) =
      plusNodes X (![0, 4, 5] i) := by
  exact (InputIdentityNodes.chart_identity X plus plus_projection _).trans
    ((rectangle_top_left _ _ _ _ i).trans
      (congrArg (fun ρ ↦ postReferenceNode (source X) (sourceMap (plus.app X))
        ρ ⟨vertices (projection.app X) (![0, 4, 5] i),
          references (projection.app X) (![0, 4, 5] i)⟩)
        (plus_total_anchor X)))

/-- The inverse polynomial columns keep their distinct original top-square references. -/
theorem minus_top_right (i : Fin 3) :
    InputIdentityNodes.chartNodes X minus minus_projection
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) =
      minusNodes X (![0, 1, 2] i) := by
  exact (InputIdentityNodes.chart_identity X minus minus_projection _).trans
    ((rectangle_top_right _ _ _ _ i).trans
      (congrArg (fun ρ ↦ postReferenceNode (source X) (sourceMap (minus.app X))
        ρ ⟨vertices (projection.app X) (![0, 1, 2] i),
          references (projection.app X) (![0, 1, 2] i)⟩)
        (minus_total_anchor X)))

theorem minus_top_left (i : Fin 3) :
    InputIdentityNodes.chartNodes X minus minus_projection
      (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) =
      minusNodes X (![0, 4, 5] i) := by
  exact (InputIdentityNodes.chart_identity X minus minus_projection _).trans
    ((rectangle_top_left _ _ _ _ i).trans
      (congrArg (fun ρ ↦ postReferenceNode (source X) (sourceMap (minus.app X))
        ρ ⟨vertices (projection.app X) (![0, 4, 5] i),
          references (projection.app X) (![0, 4, 5] i)⟩)
        (minus_total_anchor X)))

/-- The positive projection row consists of the three unchanged original binary nodes. -/
theorem projection_plus_row (i : Fin 3) :
    InputIdentityProjection.nodes X (![0, 1, 2] i) =
      binaryNodes (plus.app X) (projection.app X) i := by
  fin_cases i <;> rfl

/-- The inverse row retains its original source transport before either normalization step. -/
theorem projection_minus_row (i : Fin 3) :
    InputIdentityProjection.nodes X (![0, 3, 4] i) =
      reanchorNode (InputIdentityProjection.sourceIso X)
        (binaryNodes (minus.app X) (projection.app X) i) := by
  fin_cases i
  · apply ModelSimplex.reference_node_eq (InputIdentityProjection.source_eq X)
    simp [InputIdentityProjection.sourceIso, binaryNodes]
  · rfl
  · rfl

/-- The actual initial bottom column is the original Bass nodes under fixed Laurent identity. -/
theorem bottom_initial_column (j : Fin 5) :
    bottomNodes X (Topology.SimplexGrid.index 4 2 (j, 0)) =
      postReferenceNode (source X)
        (BoundedFlatPerfectIdentitySimplex.source (laurent.obj X)) (bottomSourceIso X)
        (InputIdentityProjection.nodes X j) := by
  have h := product_column_nodes (source X) (InputIdentityProjection.source X)
    (fun i ↦ (InputIdentityProjection.nodes X i).1) (fun i ↦ (InputIdentityProjection.nodes X i).2)
    (BoundedFlatPerfectIdentitySimplex.source (laurent.obj X))
    (BoundedFlatPerfectIdentitySimplex.identityVertices
      (laurent.obj X))
    (BoundedFlatPerfectIdentitySimplex.identityReferences
      (laurent.obj X)) (bottomSourceIso X) j 0
  change bottomNodes X (Topology.SimplexGrid.index 4 2 (j, 0)) =
    postReferenceNode (source X)
      (BoundedFlatPerfectIdentitySimplex.source (laurent.obj X))
      (bottomSourceIso X ≪≫ isoWhiskerLeft (InputIdentityProjection.source X).hom.toFunctor
        (Iso.refl _)) (InputIdentityProjection.nodes X j) at h
  exact h.trans (post_identity_anchor (source X) (InputIdentityProjection.source X)
    (BoundedFlatPerfectIdentitySimplex.source (laurent.obj X)) (bottomSourceIso X)
    (InputIdentityProjection.nodes X j))

/-- The actual first top row is the same Bass node family under fixed original base identity. -/
theorem top_initial_row (j : Fin 5) :
    middleNodes X (Topology.SimplexGrid.index 2 4 (0, j)) =
      preReferenceNode (source X) (BoundedFlatPerfectIdentitySimplex.source X) (Iso.refl _)
        (InputIdentityProjection.nodes X j) := by
  have h := product_row_nodes (source X) (BoundedFlatPerfectIdentitySimplex.source X)
    (BoundedFlatPerfectIdentitySimplex.identityVertices X)
    (BoundedFlatPerfectIdentitySimplex.identityReferences X)
    (InputIdentityProjection.source X) (fun i ↦ (InputIdentityProjection.nodes X i).1)
    (fun i ↦ (InputIdentityProjection.nodes X i).2) (Iso.refl _) 0 j
  change middleNodes X (Topology.SimplexGrid.index 2 4 (0, j)) =
    preReferenceNode (source X) (BoundedFlatPerfectIdentitySimplex.source X)
      (Iso.refl _ ≪≫ isoWhiskerRight (Iso.refl _) (InputIdentityProjection.source X).hom.toFunctor)
      (InputIdentityProjection.nodes X j) at h
  exact h.trans (pre_identity_anchor (source X) (BoundedFlatPerfectIdentitySimplex.source X)
    (InputIdentityProjection.source X) (Iso.refl _) (InputIdentityProjection.nodes X j))

theorem bottom_plus_form (i : Fin 3) :
    bottomNodes X (Topology.SimplexGrid.index 4 2 (![0, 1, 2] i, 0)) =
      postReferenceNode (source X)
        (BoundedFlatPerfectIdentitySimplex.source (laurent.obj X)) (bottomSourceIso X)
        (binaryNodes (plus.app X) (projection.app X) i) := by
  rw [bottom_initial_column, projection_plus_row]

theorem bottom_minus_form (i : Fin 3) :
    bottomNodes X (Topology.SimplexGrid.index 4 2 (![0, 3, 4] i, 0)) =
      postReferenceNode (source X)
        (BoundedFlatPerfectIdentitySimplex.source (laurent.obj X))
        (bottomSourceIso X ≪≫ isoWhiskerRight (InputIdentityProjection.sourceIso X)
          (BoundedFlatPerfectIdentitySimplex.source (laurent.obj X)).hom.toFunctor)
        (binaryNodes (minus.app X) (projection.app X) i) := by
  rw [bottom_initial_column, projection_minus_row]
  exact post_anchor_node _ _ _ _ _

theorem top_plus_form (i : Fin 3) :
    middleNodes X (Topology.SimplexGrid.index 2 4 (0, ![0, 1, 2] i)) =
      preReferenceNode (source X) (BoundedFlatPerfectIdentitySimplex.source X) (Iso.refl _)
        (binaryNodes (plus.app X) (projection.app X) i) := by
  rw [top_initial_row, projection_plus_row]

theorem top_minus_form (i : Fin 3) :
    middleNodes X (Topology.SimplexGrid.index 2 4 (0, ![0, 3, 4] i)) =
      preReferenceNode (source X) (BoundedFlatPerfectIdentitySimplex.source X)
        (isoWhiskerLeft (BoundedFlatPerfectIdentitySimplex.source X).hom.toFunctor
          (InputIdentityProjection.sourceIso X))
        (binaryNodes (minus.app X) (projection.app X) i) := by
  rw [top_initial_row, projection_minus_row,
    BoundedFlatCoefficientBassUnitHZeroNodes.pre_anchor_node]
  simp only [Iso.refl_trans]

/-- Every positive source-projection node is its unchanged bottom-column node. -/
theorem plus_source_projection (i : Fin 3) :
    InputIdentityNodes.chartNodes X plus plus_projection
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
      bottomNodes X (Topology.SimplexGrid.index 4 2 (![0, 1, 2] i, 0)) := by
  apply post_families_match (source X)
    (BoundedFlatPerfectIdentitySimplex.source (laurent.obj X))
    (BoundedFlatPerfectBinarySimplex.sourceMap (plus.app X) (projection.app X))
    (binaryNodes (plus.app X) (projection.app X))
    (fun j ↦ (InputIdentityNodes.chart_identity X plus plus_projection _).trans
      (rectangle_source_column_form _ _ _ _ j)) (bottom_plus_form X) 2 ?_ i
  exact (plus_side_right X 2).trans (plus_bottom_first X)

/-- Every inverse source-projection node retains its separate original chart reference. -/
theorem minus_source_projection (i : Fin 3) :
    InputIdentityNodes.chartNodes X minus minus_projection
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
      bottomNodes X (Topology.SimplexGrid.index 4 2 (![0, 3, 4] i, 0)) := by
  apply post_families_match (source X)
    (BoundedFlatPerfectIdentitySimplex.source (laurent.obj X))
    (BoundedFlatPerfectBinarySimplex.sourceMap (minus.app X) (projection.app X))
    (binaryNodes (minus.app X) (projection.app X))
    (fun j ↦ (InputIdentityNodes.chart_identity X minus minus_projection _).trans
      (rectangle_source_column_form _ _ _ _ j)) (bottom_minus_form X) 2 ?_ i
  exact (minus_side_right X 2).trans (minus_bottom_first X)

/-- Every positive target-projection node is the unchanged initial top-grid row. -/
theorem plus_target_projection (i : Fin 3) :
    InputIdentityNodes.chartNodes X plus plus_projection
      (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) =
      middleNodes X (Topology.SimplexGrid.index 2 4 (0, ![0, 1, 2] i)) := by
  apply pre_families_match (source X) (BoundedFlatPerfectIdentitySimplex.source X)
    (BoundedFlatPerfectBinarySimplex.sourceMap (plus.app X) (projection.app X))
    (binaryNodes (plus.app X) (projection.app X))
    (fun j ↦ (InputIdentityNodes.chart_identity X plus plus_projection _).trans
      (rectangle_target_row_form _ _ _ _ j)) (top_plus_form X) 2 ?_ i
  exact (plus_top_left X 2).trans (plus_shared X 0)

/-- The inverse target row retains both original raw and normalized comparison vertices. -/
theorem minus_target_projection (i : Fin 3) :
    InputIdentityNodes.chartNodes X minus minus_projection
      (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) =
      middleNodes X (Topology.SimplexGrid.index 2 4 (0, ![0, 3, 4] i)) := by
  apply pre_families_match (source X) (BoundedFlatPerfectIdentitySimplex.source X)
    (BoundedFlatPerfectBinarySimplex.sourceMap (minus.app X) (projection.app X))
    (binaryNodes (minus.app X) (projection.app X))
    (fun j ↦ (InputIdentityNodes.chart_identity X minus minus_projection _).trans
      (rectangle_target_row_form _ _ _ _ j)) (top_minus_form X) 2 ?_ i
  exact (minus_top_left X 2).trans (minus_shared X 0)

/-- The five actual plus side boundary nodes, in their original path order. -/
theorem h0_plus_side (i : Fin 5) :
    InputIdentityNodes.nodes X
        (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom (![9, 10, 11, 12, 13] i)) =
      plusSideNodes X (![0, 1, 2, 4, 5] i) := by
  rw [InputIdentityNodes.plus_nodes]
  fin_cases i
  · exact plus_side_right X 0
  · exact plus_side_right X 1
  · exact plus_side_right X 2
  · exact plus_side_left X 1
  · exact plus_side_left X 2

/-- The five actual plus top boundary nodes, in their original path order. -/
theorem h0_plus_top (i : Fin 5) :
    InputIdentityNodes.nodes X
        (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom (![5, 6, 13, 7, 17] i)) =
      plusNodes X (![0, 1, 2, 4, 5] i) := by
  rw [InputIdentityNodes.plus_nodes]
  fin_cases i
  · exact plus_top_right X 0
  · exact plus_top_right X 1
  · exact plus_top_right X 2
  · exact plus_top_left X 1
  · exact plus_top_left X 2

/-- The three actual plus source projection nodes retain both binary normalization steps. -/
theorem h0_plus_source (i : Fin 3) :
    InputIdentityNodes.nodes X
        (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom (![2, 3, 11] i)) =
      bottomNodes X (![0, 3, 6] i) := by
  rw [InputIdentityNodes.plus_nodes]
  fin_cases i
  · exact plus_source_projection X 0
  · exact plus_source_projection X 1
  · exact plus_source_projection X 2

/-- The three actual plus target projection nodes retain both binary normalization steps. -/
theorem h0_plus_target (i : Fin 3) :
    InputIdentityNodes.nodes X
        (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom (![15, 16, 17] i)) =
      middleNodes X (![0, 1, 2] i) := by
  rw [InputIdentityNodes.plus_nodes]
  fin_cases i
  · exact plus_target_projection X 0
  · exact plus_target_projection X 1
  · exact plus_target_projection X 2

/-- The five actual minus side boundary nodes, in their original path order. -/
theorem h0_minus_side (i : Fin 5) :
    InputIdentityNodes.nodes X
        (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom (![9, 10, 11, 12, 13] i)) =
      minusSideNodes X (![0, 1, 2, 4, 5] i) := by
  rw [InputIdentityNodes.minus_nodes]
  fin_cases i
  · exact minus_side_right X 0
  · exact minus_side_right X 1
  · exact minus_side_right X 2
  · exact minus_side_left X 1
  · exact minus_side_left X 2

/-- The five actual minus top boundary nodes, in their original path order. -/
theorem h0_minus_top (i : Fin 5) :
    InputIdentityNodes.nodes X
        (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom (![5, 6, 13, 7, 17] i)) =
      minusNodes X (![0, 1, 2, 4, 5] i) := by
  rw [InputIdentityNodes.minus_nodes]
  fin_cases i
  · exact minus_top_right X 0
  · exact minus_top_right X 1
  · exact minus_top_right X 2
  · exact minus_top_left X 1
  · exact minus_top_left X 2

/-- The three actual minus source projection nodes retain both binary normalization steps. -/
theorem h0_minus_source (i : Fin 3) :
    InputIdentityNodes.nodes X
        (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom (![2, 3, 11] i)) =
      bottomNodes X (![0, 9, 12] i) := by
  rw [InputIdentityNodes.minus_nodes]
  fin_cases i
  · exact minus_source_projection X 0
  · exact minus_source_projection X 1
  · exact minus_source_projection X 2

/-- The three actual minus target projection nodes retain both binary normalization steps. -/
theorem h0_minus_target (i : Fin 3) :
    InputIdentityNodes.nodes X
        (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom (![15, 16, 17] i)) =
      middleNodes X (![0, 3, 4] i) := by
  rw [InputIdentityNodes.minus_nodes]
  fin_cases i
  · exact minus_target_projection X 0
  · exact minus_target_projection X 1
  · exact minus_target_projection X 2

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityBoundaryNodes
