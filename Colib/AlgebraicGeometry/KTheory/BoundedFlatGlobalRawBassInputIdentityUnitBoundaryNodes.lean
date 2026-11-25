/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityCarrierBottom
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityCarrierProjection
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityTopNodes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassUnitTopChartJoins

/-!
# Complete reference nodes of the original raw global identity unit boundary

The literal Laurent identity product and the literal base unit product retain the same
five terminal projection nodes and both signed unit-square sides, not just their
evaluations in a spectrum.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityUnitBoundaryNodes
open BoundedFlatPerfectOriginalUnitSquareSimplex InputIdentityTopNodes InputIdentityTopSimplex
open Topology Topology.LoopPrespectrum
open InputIdentityCarrierProjection (right_route_identity)
local notation "Wₛ" => BoundedFlatPerfectTripleSimplex.structureOn

/-- The original left route has the same literal identity composite. -/
theorem left_route_identity {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (leftFirst f).hom ≫ (leftSecond f).hom = 𝟙 _ :=
  (two_routes f).symm.trans (right_route_identity f)

/-- The first right unit transformation is the actual inverse of its terminal unit. -/
theorem right_first_inverse {X Y : Scheme.{u}} (f : X ⟶ Y) :
    rightFirst f = (rightSecond f).symm := by
  apply Iso.ext
  apply (cancel_mono (rightSecond f).hom).1
  rw [right_route_identity, Iso.symm_hom, Iso.inv_hom_id]

/-- The first left unit transformation is the actual inverse of its terminal unit. -/
theorem left_first_inverse {X Y : Scheme.{u}} (f : X ⟶ Y) :
    leftFirst f = (leftSecond f).symm := by
  apply Iso.ext
  apply (cancel_mono (leftSecond f).hom).1
  rw [left_route_identity, Iso.symm_hom, Iso.inv_hom_id]

/-- The middle geometric identity transformation is the same under the two actual whiskerings. -/
theorem shared_second {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B) :
    isoWhiskerRight (rightSecond p) (sourceMap q).hom.toFunctor =
      isoWhiskerLeft (sourceMap p).hom.toFunctor (leftSecond q) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [rightSecond, leftSecond, boundedAboveFlatPerfectNormalizedRightUnitSecond,
    boundedAboveFlatPerfectNormalizedLeftUnitSecond, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    Iso.trans_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    leftUnitor_hom_app, rightUnitor_hom_app]
  rfl

/-- Equality of the original unit inverses identifies the shared initial reference. -/
theorem shared_first {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B) :
    isoWhiskerRight (rightFirst p) (sourceMap q).hom.toFunctor =
      isoWhiskerLeft (sourceMap p).hom.toFunctor (leftFirst q) := by
  rw [right_first_inverse, left_first_inverse]
  exact congrArg Iso.symm (shared_second p q)

/-- The original split geometric normalization step is also preserved, not only its composite. -/
theorem shared_geometric {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B) :
    isoWhiskerRight (rightSecondGeometric p) (sourceMap q).hom.toFunctor =
      isoWhiskerLeft (sourceMap p).hom.toFunctor (leftSecondGeometric q) := by
  rfl

/-- The whole left unit is the actual two-step original identity, whiskered by pullback. -/
theorem left_second_total {A B : Scheme.{u}} (p : B ⟶ A) :
    leftSecond p = isoWhiskerRight (BoundedFlatPerfectIdentitySimplex.first A ≪≫
      BoundedFlatPerfectIdentitySimplex.second A) (sourceMap p).hom.toFunctor := by
  apply Iso.ext
  rw [← left_second_composite]
  simp only [isoWhiskerRight_hom, Iso.trans_hom, whiskerRight_comp]
  rfl

/-- Naturality transports a chart anchor through the actual two-step identity transformation. -/
theorem chart_anchor {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B)
    (S : asSmallCategory (Wₛ A) ⟶
      asSmallCategory (Wₛ C))
    (σ : S.hom.toFunctor ≅ (sourceMap p ≫ sourceMap q).hom.toFunctor) :
    isoWhiskerLeft (BoundedFlatPerfectIdentitySimplex.source A).hom.toFunctor σ ≪≫
        (isoWhiskerRight (leftFirst p) (sourceMap q).hom.toFunctor).symm =
      isoWhiskerRight (BoundedFlatPerfectIdentitySimplex.first A ≪≫
        BoundedFlatPerfectIdentitySimplex.second A) S.hom.toFunctor ≪≫ σ := by
  rw [left_first_inverse]
  change isoWhiskerLeft (BoundedFlatPerfectIdentitySimplex.source A).hom.toFunctor σ ≪≫
      isoWhiskerRight (leftSecond p) (sourceMap q).hom.toFunctor = _
  rw [left_second_total]
  change isoWhiskerLeft (BoundedFlatPerfectIdentitySimplex.source A).hom.toFunctor σ ≪≫
      isoWhiskerRight (BoundedFlatPerfectIdentitySimplex.first A ≪≫
        BoundedFlatPerfectIdentitySimplex.second A) (sourceMap p ≫ sourceMap q).hom.toFunctor = _
  exact isoWhiskerLeft_trans_isoWhiskerRight _ _

/-- The Laurent identity is the complete right-unit transformation under pullback. -/
theorem right_second_total {A B : Scheme.{u}} (q : B ⟶ A) :
    rightSecond q = isoWhiskerLeft (sourceMap q).hom.toFunctor
      (BoundedFlatPerfectIdentitySimplex.first B ≪≫ BoundedFlatPerfectIdentitySimplex.second B)
      := by
  apply Iso.ext
  rw [← right_second_composite]
  simp only [isoWhiskerLeft_hom, Iso.trans_hom, whiskerLeft_comp]
  rfl

/-- The split geometric right-unit step is the original first identity transformation. -/
theorem right_geometric_total {A B : Scheme.{u}} (q : B ⟶ A) :
    rightSecondGeometric q = isoWhiskerLeft (sourceMap q).hom.toFunctor
      (BoundedFlatPerfectIdentitySimplex.first B) := rfl

variable (X : Scheme.{u})

/-- The original positive Laurent unit square, precomposed with the polynomial projection. -/
def plusSideNodes (i : Fin 8) : Node X :=
  ⟨sourceMap (projection.app X) ≫ vertices (plus.app X) i,
    plusSourceIso X ≪≫ isoWhiskerLeft (sourceMap (projection.app X)).hom.toFunctor
      (references (plus.app X) i)⟩

/-- The original inverse Laurent unit square retains its separate reference anchor. -/
def minusSideNodes (i : Fin 8) : Node X :=
  ⟨sourceMap (projection.app X) ≫ vertices (minus.app X) i,
    minusSourceIso X ≪≫ isoWhiskerLeft (sourceMap (projection.app X)).hom.toFunctor
      (references (minus.app X) i)⟩

theorem plus_top_first : plusSideNodes X 5 = plusNodes X 2 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso X ≪≫ isoWhiskerLeft
    (sourceMap (projection.app X)).hom.toFunctor (leftFirst (plus.app X))).hom =
    (plusSourceIso X ≪≫ isoWhiskerRight (rightFirst (projection.app X))
      (sourceMap (plus.app X)).hom.toFunctor).hom
  rw [shared_first]

theorem minus_top_first : minusSideNodes X 5 = minusNodes X 2 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso X ≪≫ isoWhiskerLeft
    (sourceMap (projection.app X)).hom.toFunctor (leftFirst (minus.app X))).hom =
    (minusSourceIso X ≪≫ isoWhiskerRight (rightFirst (projection.app X))
      (sourceMap (minus.app X)).hom.toFunctor).hom
  rw [shared_first]

theorem plus_top_intermediate : plusSideNodes X 6 = plusNodes X 3 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso X ≪≫ isoWhiskerLeft
    (sourceMap (projection.app X)).hom.toFunctor
    (leftFirst (plus.app X) ≪≫ leftSecondGeometric (plus.app X))).hom =
    (plusSourceIso X ≪≫ isoWhiskerRight
      (rightFirst (projection.app X) ≪≫
        rightSecondGeometric (projection.app X))
      (sourceMap (plus.app X)).hom.toFunctor).hom
  simp only [isoWhiskerLeft_trans, isoWhiskerRight_trans, shared_first, shared_geometric]

theorem minus_top_intermediate : minusSideNodes X 6 = minusNodes X 3 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso X ≪≫ isoWhiskerLeft
    (sourceMap (projection.app X)).hom.toFunctor
    (leftFirst (minus.app X) ≪≫ leftSecondGeometric (minus.app X))).hom =
    (minusSourceIso X ≪≫ isoWhiskerRight
      (rightFirst (projection.app X) ≪≫
        rightSecondGeometric (projection.app X))
      (sourceMap (minus.app X)).hom.toFunctor).hom
  simp only [isoWhiskerLeft_trans, isoWhiskerRight_trans, shared_first, shared_geometric]

theorem plus_top_target : plusSideNodes X 7 = plusNodes X 7 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso X ≪≫ isoWhiskerLeft
    (sourceMap (projection.app X)).hom.toFunctor
    (rightFirst (plus.app X) ≪≫ rightSecond (plus.app X))).hom =
    (plusSourceIso X ≪≫ isoWhiskerRight
      (rightFirst (projection.app X) ≪≫ rightSecond (projection.app X))
      (sourceMap (plus.app X)).hom.toFunctor).hom
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, right_route_identity,
    whiskerLeft_id', whiskerRight_id']

theorem minus_top_target : minusSideNodes X 7 = minusNodes X 7 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso X ≪≫ isoWhiskerLeft
    (sourceMap (projection.app X)).hom.toFunctor
    (rightFirst (minus.app X) ≪≫ rightSecond (minus.app X))).hom =
    (minusSourceIso X ≪≫ isoWhiskerRight
      (rightFirst (projection.app X) ≪≫ rightSecond (projection.app X))
      (sourceMap (minus.app X)).hom.toFunctor).hom
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, right_route_identity,
    whiskerLeft_id', whiskerRight_id']

/-- The original source-to-projection isomorphism on the unit boundary. -/
abbrev sourceToProjection := InputIdentityNodes.sourceToProjection X

private theorem map_identity_comp {V W : Type*} [Category V] [Category W] (F : V ⥤ W)
    (X : V) {Y : W} (η : F.obj X ⟶ Y) : F.map (𝟙 X) ≫ η = η :=
  (congrArg (fun f ↦ f ≫ η) (F.map_id X)).trans (Category.id_comp η)

private theorem middle_initial_reference (j : Fin 5) :
    productReference X 0 j =
      isoWhiskerLeft (BoundedFlatPerfectIdentitySimplex.source X).hom.toFunctor
        (InputIdentityProjection.nodes X j).2 := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  change (InputIdentityProjection.source X).hom.toFunctor.map
      (𝟙 ((BoundedFlatPerfectIdentitySimplex.source X).hom.toFunctor.obj A)) ≫
    (InputIdentityProjection.nodes X j).2.hom.app
      ((BoundedFlatPerfectIdentitySimplex.source X).hom.toFunctor.obj A) =
    (InputIdentityProjection.nodes X j).2.hom.app
      ((BoundedFlatPerfectIdentitySimplex.source X).hom.toFunctor.obj A)
  exact map_identity_comp _ _ _

/-- The positive anchor is the same actual projection reference, followed by its chart total. -/
theorem plus_anchor : plusSourceIso X =
    sourceToProjection X ≪≫ (InputIdentityProjection.nodes X 2).2 := by
  change productReference X 0 2 ≪≫
    (isoWhiskerRight (leftFirst (projection.app X))
      (sourceMap (plus.app X)).hom.toFunctor).symm = _
  exact (congrArg (fun ρ ↦ ρ ≪≫
    (isoWhiskerRight (leftFirst (projection.app X))
      (sourceMap (plus.app X)).hom.toFunctor).symm)
    (middle_initial_reference X 2)).trans (chart_anchor _ _ _ _)

/-- The inverse anchor uses that identical projection reference and its transported chart total. -/
theorem minus_anchor : minusSourceIso X =
    sourceToProjection X ≪≫ (InputIdentityProjection.nodes X 4).2 := by
  change productReference X 0 4 ≪≫
    (isoWhiskerRight (leftFirst (projection.app X))
      (sourceMap (minus.app X)).hom.toFunctor).symm = _
  exact (congrArg (fun ρ ↦ ρ ≪≫
    (isoWhiskerRight (leftFirst (projection.app X))
      (sourceMap (minus.app X)).hom.toFunctor).symm)
    (middle_initial_reference X 4)).trans (chart_anchor _ _ _ _)

/-- The actual original projection-by-Laurent-unit source. -/
abbrev bottomSource := InputIdentityCarrierBottom.productSource X
/-- The already constructed full common-reference transport of that product. -/
abbrev bottomSourceIso := InputIdentityCarrierBottom.sourceIso X
/-- The actual original fifteen-node product, with no replacement references. -/
abbrev bottomNodes := InputIdentityCarrierBottom.nodes X

/-- The original bottom reference at an explicit pair of product vertices. -/
def bottomPairReference (j : Fin 5) (k : Fin 3) : (source X).hom.toFunctor ≅
    ((InputIdentityProjection.nodes X j).1 ≫
      BoundedFlatPerfectIdentitySimplex.identityVertices
        (laurent.obj X) k).hom.toFunctor :=
  bottomSourceIso X ≪≫ (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
    ((InputIdentityProjection.nodes X j).2.prod
      (BoundedFlatPerfectIdentitySimplex.identityReferences
        (laurent.obj X) k))

/-- Naturality retains both original identity-normalization steps of the bottom reference. -/
theorem bottom_pair_reference (j : Fin 5) (k : Fin 3) :
    bottomPairReference X j k =
      (sourceToProjection X ≪≫ (InputIdentityProjection.nodes X j).2) ≪≫
        isoWhiskerLeft (InputIdentityProjection.nodes X j).1.hom.toFunctor
          ((BoundedFlatPerfectIdentitySimplex.first (laurent.obj X) ≪≫
              BoundedFlatPerfectIdentitySimplex.second (laurent.obj X)).symm ≪≫
            BoundedFlatPerfectIdentitySimplex.identityReferences
              (laurent.obj X) k) := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  let τ := BoundedFlatPerfectIdentitySimplex.first (laurent.obj X) ≪≫
    BoundedFlatPerfectIdentitySimplex.second (laurent.obj X)
  let σ := (InputIdentityProjection.nodes X j).2
  let ρ := BoundedFlatPerfectIdentitySimplex.identityReferences
    (laurent.obj X) k
  change ((sourceToProjection X).hom.app A ≫
      τ.inv.app ((InputIdentityProjection.source X).hom.toFunctor.obj A)) ≫
      ((BoundedFlatPerfectIdentitySimplex.source (laurent.obj X)).hom.toFunctor.map
          (σ.hom.app A) ≫ ρ.hom.app ((InputIdentityProjection.nodes X j).1.hom.toFunctor.obj A)) =
    ((sourceToProjection X).hom.app A ≫ σ.hom.app A) ≫
      (τ.inv.app ((InputIdentityProjection.nodes X j).1.hom.toFunctor.obj A) ≫
        ρ.hom.app ((InputIdentityProjection.nodes X j).1.hom.toFunctor.obj A))
  simp only [Category.assoc]
  rw [← τ.inv.naturality_assoc]
  rfl

/-- The row-major product enumeration preserves its actual entire dependent reference node. -/
theorem bottom_pair (j : Fin 5) (k : Fin 3) :
    bottomNodes X (SimplexGrid.index 4 2 (j, k)) =
      ⟨(InputIdentityProjection.nodes X j).1 ≫
        BoundedFlatPerfectIdentitySimplex.identityVertices
          (laurent.obj X) k,
        bottomPairReference X j k⟩ := by
  exact congrArg (fun z : Fin 5 × Fin 3 ↦
    (⟨(InputIdentityProjection.nodes X z.1).1 ≫
      BoundedFlatPerfectIdentitySimplex.identityVertices
        (laurent.obj X) z.2,
      bottomPairReference X z.1 z.2⟩ : InputIdentityNodes.Node X))
    (SimplexGrid.decode_index 4 2 (j, k))

/-- Every terminal bottom reference is the same actual projection reference followed by its node. -/
theorem bottom_terminal_reference (j : Fin 5) : bottomPairReference X j 2 =
    sourceToProjection X ≪≫ (InputIdentityProjection.nodes X j).2 := by
  rw [bottom_pair_reference]
  change _ ≪≫ isoWhiskerLeft _ ((_ ≪≫ _).symm ≪≫ (_ ≪≫ _)) = _
  simp

theorem plus_bottom_first : plusSideNodes X 2 = bottomNodes X 6 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso X ≪≫ isoWhiskerLeft
    (sourceMap (projection.app X)).hom.toFunctor (rightFirst (plus.app X))).hom =
      (bottomPairReference X 2 0).hom
  rw [right_first_inverse, right_second_total, bottom_pair_reference, plus_anchor]
  simp only [BoundedFlatPerfectIdentitySimplex.identityReferences, Fin.cases_zero,
    Iso.trans_refl]
  rfl

theorem minus_bottom_first : minusSideNodes X 2 = bottomNodes X 12 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso X ≪≫ isoWhiskerLeft
    (sourceMap (projection.app X)).hom.toFunctor (rightFirst (minus.app X))).hom =
      (bottomPairReference X 4 0).hom
  rw [right_first_inverse, right_second_total, bottom_pair_reference, minus_anchor]
  simp only [BoundedFlatPerfectIdentitySimplex.identityReferences, Fin.cases_zero,
    Iso.trans_refl]
  rfl

theorem plus_bottom_intermediate : plusSideNodes X 3 = bottomNodes X 7 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso X ≪≫ isoWhiskerLeft
    (sourceMap (projection.app X)).hom.toFunctor
    (rightFirst (plus.app X) ≪≫ rightSecondGeometric (plus.app X))).hom =
      (bottomPairReference X 2 1).hom
  rw [right_first_inverse, right_second_total, right_geometric_total,
    bottom_pair_reference, plus_anchor]
  rfl

theorem minus_bottom_intermediate : minusSideNodes X 3 = bottomNodes X 13 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso X ≪≫ isoWhiskerLeft
    (sourceMap (projection.app X)).hom.toFunctor
    (rightFirst (minus.app X) ≪≫ rightSecondGeometric (minus.app X))).hom =
      (bottomPairReference X 4 1).hom
  rw [right_first_inverse, right_second_total, right_geometric_total,
    bottom_pair_reference, minus_anchor]
  rfl

theorem plus_bottom_target : plusSideNodes X 7 = bottomNodes X 8 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso X ≪≫ isoWhiskerLeft
    (sourceMap (projection.app X)).hom.toFunctor
    (rightFirst (plus.app X) ≪≫ rightSecond (plus.app X))).hom =
      (bottomPairReference X 2 2).hom
  rw [bottom_terminal_reference, ← plus_anchor]
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, right_route_identity,
    whiskerLeft_id']
  exact Category.comp_id _

theorem minus_bottom_target : minusSideNodes X 7 = bottomNodes X 14 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso X ≪≫ isoWhiskerLeft
    (sourceMap (projection.app X)).hom.toFunctor
    (rightFirst (minus.app X) ≪≫ rightSecond (minus.app X))).hom =
      (bottomPairReference X 4 2).hom
  rw [bottom_terminal_reference, ← minus_anchor]
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, right_route_identity,
    whiskerLeft_id']
  exact Category.comp_id _

/-- All five terminal projection vertices share their complete original references. -/
theorem terminal_nodes (j : Fin 5) :
    bottomNodes X (SimplexGrid.index 4 2 (j, 2)) =
      middleNodes X (SimplexGrid.index 2 4 (2, j)) := by
  rw [bottom_pair, middle_pair]
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  rw [bottom_terminal_reference]
  rfl

/-- All positive top joins are full node equalities, including the normalization intermediate. -/
theorem plus_top_nodes (i : Fin 3) : plusSideNodes X (![5, 6, 7] i) =
    plusNodes X (![2, 3, 7] i) := by
  fin_cases i
  · exact plus_top_first X
  · exact plus_top_intermediate X
  · exact plus_top_target X

/-- All inverse-chart top joins retain their actual full dependent references. -/
theorem minus_top_nodes (i : Fin 3) : minusSideNodes X (![5, 6, 7] i) =
    minusNodes X (![2, 3, 7] i) := by
  fin_cases i
  · exact minus_top_first X
  · exact minus_top_intermediate X
  · exact minus_top_target X

/-- The positive Laurent identity edge agrees with its original bottom product column. -/
theorem plus_bottom_nodes (i : Fin 3) : plusSideNodes X (![2, 3, 7] i) =
    bottomNodes X (![6, 7, 8] i) := by
  fin_cases i
  · exact plus_bottom_first X
  · exact plus_bottom_intermediate X
  · exact plus_bottom_target X

/-- The inverse Laurent identity edge agrees with its separate original bottom column. -/
theorem minus_bottom_nodes (i : Fin 3) : minusSideNodes X (![2, 3, 7] i) =
    bottomNodes X (![12, 13, 14] i) := by
  fin_cases i
  · exact minus_bottom_first X
  · exact minus_bottom_intermediate X
  · exact minus_bottom_target X


/-- The actual positive rectangle total is exactly the original top/side reference anchor. -/
theorem plus_total_anchor :
    InputIdentityNodes.chartProjectionIso X plus plus_projection ≪≫
      BoundedFlatPerfectBinarySimplex.total (plus.app X) (projection.app X) = plusSourceIso X := by
  rw [plus_anchor]
  change (sourceToProjection X ≪≫ eqToIso rfl) ≪≫
      BoundedFlatPerfectBinarySimplex.total (plus.app X) (projection.app X) =
    sourceToProjection X ≪≫
      BoundedFlatPerfectBinarySimplex.total (plus.app X) (projection.app X)
  simp only [eqToIso_refl, Iso.trans_refl]

/-- The inverse rectangle retains its original geometric source transport before the total. -/
theorem minus_total_anchor :
    InputIdentityNodes.chartProjectionIso X minus minus_projection ≪≫
      BoundedFlatPerfectBinarySimplex.total (minus.app X) (projection.app X) =
        minusSourceIso X := by
  rw [minus_anchor]
  change (sourceToProjection X ≪≫ InputIdentityProjection.sourceIso X) ≪≫ _ =
    sourceToProjection X ≪≫ (InputIdentityProjection.sourceIso X ≪≫ _)
  exact Iso.trans_assoc _ _ _

/-- All positive unit nodes retain exactly the frozen chart's complete source reference. -/
theorem plus_side_actual (i : Fin 8) : plusSideNodes X i =
    InputIdentityNodes.chartSideNodes X plus plus_projection i := by
  change ModelSimplex.preReferenceNode (source X) (sourceMap (projection.app X)) (plusSourceIso X)
      ⟨vertices (plus.app X) i, references (plus.app X) i⟩ =
    ModelSimplex.preReferenceNode (source X) (sourceMap (projection.app X))
      (InputIdentityNodes.chartProjectionIso X plus plus_projection ≪≫
        BoundedFlatPerfectBinarySimplex.total (plus.app X) (projection.app X))
      ⟨vertices (plus.app X) i, references (plus.app X) i⟩
  rw [plus_total_anchor]

/-- Every inverse unit node retains its distinct original map and the same actual chart anchor. -/
theorem minus_side_actual (i : Fin 8) : minusSideNodes X i =
    InputIdentityNodes.chartSideNodes X minus minus_projection i := by
  change ModelSimplex.preReferenceNode (source X) (sourceMap (projection.app X)) (minusSourceIso X)
      ⟨vertices (minus.app X) i, references (minus.app X) i⟩ =
    ModelSimplex.preReferenceNode (source X) (sourceMap (projection.app X))
      (InputIdentityNodes.chartProjectionIso X minus minus_projection ≪≫
        BoundedFlatPerfectBinarySimplex.total (minus.app X) (projection.app X))
      ⟨vertices (minus.app X) i, references (minus.app X) i⟩
  rw [minus_total_anchor]

/-- The entire bottom terminal column is the actual unpaused projection carrier node family. -/
theorem bottom_terminal_nodes (j : Fin 5) :
    bottomNodes X (SimplexGrid.index 4 2 (j, 2)) =
      InputIdentityCarrierProjection.nodes X j := by
  rw [bottom_pair]
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  rw [bottom_terminal_reference]

/-- The whole top terminal row has exactly those same original projection nodes and references. -/
theorem middle_terminal_nodes (j : Fin 5) :
    middleNodes X (SimplexGrid.index 2 4 (2, j)) =
      InputIdentityCarrierProjection.nodes X j :=
  (terminal_nodes X j).symm.trans (bottom_terminal_nodes X j)

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityUnitBoundaryNodes
