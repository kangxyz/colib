/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityTopSimplex
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassUnitTopChartJoins
public import Colib.KTheory.Waldhausen.Iterated.ReferenceWhiskeringFamily

/-!
# The actual shared nodes of the original global span identity

The original global scheme arrows and full reference data are used directly. Only the pure
scalar parameters are shared with the coefficient development; no coefficient model is identified.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Topology Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityTopNodes
open BoundedFlatPerfectOriginalUnitSquareSimplex InputIdentityTopSimplex
local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

variable (X : Scheme.{u})

/-- The unchanged reference of the literal product grid. -/
abbrev source := BoundedFlatPerfectIdentitySimplex.source X ≫ InputIdentityProjection.source X

/-- A model-map node with an isomorphism from the fixed product-grid reference. -/
abbrev Node := Σ F : asSmallCategory (W X) ⟶
    asSmallCategory (W (laurent.obj X)), (source X).hom.toFunctor ≅ F.hom.toFunctor

/-- All fifteen original product nodes, with their original product references. -/
def middleNodes (i : Fin 15) : Node X :=
  ⟨CommonReferenceProduct.vertices (BoundedFlatPerfectIdentitySimplex.identityVertices X)
      (fun j ↦ (InputIdentityProjection.nodes X j).1) i,
    CommonReferenceProduct.references (BoundedFlatPerfectIdentitySimplex.source X)
      (BoundedFlatPerfectIdentitySimplex.identityVertices X)
        (BoundedFlatPerfectIdentitySimplex.identityReferences X)
      (InputIdentityProjection.source X) (fun j ↦ (InputIdentityProjection.nodes X j).1)
      (fun j ↦ (InputIdentityProjection.nodes X j).2) i⟩

/-- The positive square changes reference through its actual shared initial identity node. -/
def plusSourceIso : (source X).hom.toFunctor ≅
    (sourceMap (projection.app X) ≫ sourceMap (plus.app X)).hom.toFunctor :=
  (middleNodes X 2).2 ≪≫
    (isoWhiskerRight (leftFirst (projection.app X))
      (sourceMap (plus.app X)).hom.toFunctor).symm

/-- The negative square uses the actual inverse-chart node, including its source transport. -/
def minusSourceIso : (source X).hom.toFunctor ≅
    (sourceMap (projection.app X) ≫ sourceMap (minus.app X)).hom.toFunctor :=
  (middleNodes X 4).2 ≪≫
    (isoWhiskerRight (leftFirst (projection.app X))
      (sourceMap (minus.app X)).hom.toFunctor).symm

/-- Every positive vertex and its original reference, whiskered by the positive chart. -/
def plusNodes (i : Fin 8) : Node X :=
  ⟨vertices (projection.app X) i ≫ sourceMap (plus.app X),
    plusSourceIso X ≪≫ isoWhiskerRight (references (projection.app X) i)
      (sourceMap (plus.app X)).hom.toFunctor⟩

/-- Every negative vertex and its original reference, whiskered by the negative chart. -/
def minusNodes (i : Fin 8) : Node X :=
  ⟨vertices (projection.app X) i ≫ sourceMap (minus.app X),
    minusSourceIso X ≪≫ isoWhiskerRight (references (projection.app X) i)
      (sourceMap (minus.app X)).hom.toFunctor⟩

theorem plus_five : plusNodes X 5 = middleNodes X 2 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (((middleNodes X 2).2 ≪≫
    (isoWhiskerRight (leftFirst (projection.app X))
      (sourceMap (plus.app X)).hom.toFunctor).symm) ≪≫
    isoWhiskerRight (leftFirst (projection.app X))
      (sourceMap (plus.app X)).hom.toFunctor).hom = (middleNodes X 2).2.hom
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem minus_five : minusNodes X 5 = middleNodes X 4 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (((middleNodes X 4).2 ≪≫
    (isoWhiskerRight (leftFirst (projection.app X))
      (sourceMap (minus.app X)).hom.toFunctor).symm) ≪≫
    isoWhiskerRight (leftFirst (projection.app X))
      (sourceMap (minus.app X)).hom.toFunctor).hom = (middleNodes X 4).2.hom
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The literal pair of references before enumerating the product grid. -/
def productReference (i : Fin 3) (j : Fin 5) : (source X).hom.toFunctor ≅
    (BoundedFlatPerfectIdentitySimplex.identityVertices X i ≫
      (InputIdentityProjection.nodes X j).1).hom.toFunctor :=
  (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
    ((BoundedFlatPerfectIdentitySimplex.identityReferences X i).prod
      (InputIdentityProjection.nodes X j).2)

/-- Naturality of the actual product reference moves the split base-unit comparison right. -/
theorem product_reference (i : Fin 3) (j : Fin 5) :
    productReference X i j = productReference X 0 j ≪≫
      isoWhiskerRight (BoundedFlatPerfectIdentitySimplex.identityReferences X i)
        (InputIdentityProjection.nodes X j).1.hom.toFunctor := by
  unfold productReference
  rw [CommonReferenceProduct.composition_pair_iso_other
    (BoundedFlatPerfectIdentitySimplex.identityReferences X i)
      (InputIdentityProjection.nodes X j).2,
    CommonReferenceProduct.composition_pair_iso_other
      (BoundedFlatPerfectIdentitySimplex.identityReferences X 0)
        (InputIdentityProjection.nodes X j).2]
  change _ = (_ ≪≫ isoWhiskerRight (Iso.refl _) _) ≪≫ _
  rw [isoWhiskerRight_refl, Iso.trans_refl]

/-- Decoding a product index preserves the entire dependent node. -/
theorem middle_pair (i : Fin 3) (j : Fin 5) :
    middleNodes X (SimplexGrid.index 2 4 (i, j)) =
      ⟨BoundedFlatPerfectIdentitySimplex.identityVertices X i ≫
        (InputIdentityProjection.nodes X j).1,
        productReference X i j⟩ := by
  exact congrArg (fun z : Fin 3 × Fin 5 ↦
    (⟨BoundedFlatPerfectIdentitySimplex.identityVertices X z.1 ≫
      (InputIdentityProjection.nodes X z.2).1,
      productReference X z.1 z.2⟩ : Node X))
    (SimplexGrid.decode_index 2 4 (i, j))

theorem plus_six : plusNodes X 6 = middleNodes X 7 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso X ≪≫ isoWhiskerRight
    (leftFirst (projection.app X) ≪≫ leftSecondGeometric (projection.app X))
    (sourceMap (plus.app X)).hom.toFunctor).hom = (productReference X 1 2).hom
  rw [product_reference]
  simp only [plusSourceIso, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    isoWhiskerRight_inv, whiskerRight_comp, Category.assoc]
  simp only [← whiskerRight_comp, Iso.inv_hom_id_assoc]
  rfl

theorem minus_six : minusNodes X 6 = middleNodes X 9 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso X ≪≫ isoWhiskerRight
    (leftFirst (projection.app X) ≪≫ leftSecondGeometric (projection.app X))
    (sourceMap (minus.app X)).hom.toFunctor).hom = (productReference X 1 4).hom
  rw [product_reference]
  simp only [minusSourceIso, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    isoWhiskerRight_inv, whiskerRight_comp, Category.assoc]
  simp only [← whiskerRight_comp, Iso.inv_hom_id_assoc]
  rfl

private theorem left_second_whisker {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B) :
    whiskerRight (leftSecond p).hom (sourceMap q).hom.toFunctor =
      whiskerRight ((BoundedFlatPerfectIdentitySimplex.first A).hom ≫
        (BoundedFlatPerfectIdentitySimplex.second A).hom)
        (sourceMap p ≫ sourceMap q).hom.toFunctor := by
  rw [← left_second_composite]
  simp only [whiskerRight_comp]
  rfl

theorem plus_seven : plusNodes X 7 = middleNodes X 12 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso X ≪≫ isoWhiskerRight
    (rightFirst (projection.app X) ≪≫ rightSecond (projection.app X))
    (sourceMap (plus.app X)).hom.toFunctor).hom = (productReference X 2 2).hom
  rw [product_reference]
  simp only [plusSourceIso, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    isoWhiskerRight_inv]
  rw [two_routes, whiskerRight_comp]
  simp only [Category.assoc]
  simp only [← whiskerRight_comp, Iso.inv_hom_id_assoc]
  rw [left_second_whisker]
  rfl

theorem minus_seven : minusNodes X 7 = middleNodes X 14 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso X ≪≫ isoWhiskerRight
    (rightFirst (projection.app X) ≪≫ rightSecond (projection.app X))
    (sourceMap (minus.app X)).hom.toFunctor).hom = (productReference X 2 4).hom
  rw [product_reference]
  simp only [minusSourceIso, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    isoWhiskerRight_inv]
  rw [two_routes, whiskerRight_comp]
  simp only [Category.assoc]
  simp only [← whiskerRight_comp, Iso.inv_hom_id_assoc]
  rw [left_second_whisker]
  rfl

/-- All three positive shared vertices agree as dependent nodes, including reference transport. -/
theorem plus_shared (i : Fin 3) :
    plusNodes X ⟨5 + i.val, by omega⟩ =
      middleNodes X ⟨5 * i.val + 2, by omega⟩ := by
  fin_cases i
  · exact plus_five X
  · exact plus_six X
  · exact plus_seven X

/-- All three negative shared vertices retain the actual inverse-chart reference. -/
theorem minus_shared (i : Fin 3) :
    minusNodes X ⟨5 + i.val, by omega⟩ =
      middleNodes X ⟨5 * i.val + 4, by omega⟩ := by
  fin_cases i
  · exact minus_five X
  · exact minus_six X
  · exact minus_seven X

private theorem postcomp_ofIsos {V U T : WideSubcategory preservesZero.{u}} {k : ℕ}
    (F₀ : V ⟶ U) (F : Fin (k + 1) → (V ⟶ U))
    (ρ : ∀ i, F₀.hom.toFunctor ≅ (F i).hom.toFunctor) (J : U ⟶ T) :
    (ModelSimplex.ofIsos F₀ F ρ).postcomp J =
      ModelSimplex.ofIsos (F₀ ≫ J) (fun i ↦ F i ≫ J)
        (fun i ↦ isoWhiskerRight (ρ i) J.hom.toFunctor) := by
  apply ModelSimplex.ext_diagram
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro i j f
  apply heq_of_eq
  exact whiskerRight_comp _ _ _

/-- Reanchoring preserves the entire original positive square simplex. -/
theorem plus_family :
    ModelSimplex.ofIsos (source X) (fun i ↦ (plusNodes X i).1)
      (fun i ↦ (plusNodes X i).2) = plusSimplex X := by
  change ModelSimplex.ofIsos (source X)
    (fun i ↦ vertices (projection.app X) i ≫ sourceMap (plus.app X))
    (fun i ↦ plusSourceIso X ≪≫ isoWhiskerRight (references (projection.app X) i)
      (sourceMap (plus.app X)).hom.toFunctor) = _
  rw [ModelSimplex.ofIsos_change_reference]
  exact (postcomp_ofIsos _ _ _ _).symm

/-- Reanchoring preserves the entire original inverse-chart square simplex. -/
theorem minus_family :
    ModelSimplex.ofIsos (source X) (fun i ↦ (minusNodes X i).1)
      (fun i ↦ (minusNodes X i).2) = minusSimplex X := by
  change ModelSimplex.ofIsos (source X)
    (fun i ↦ vertices (projection.app X) i ≫ sourceMap (minus.app X))
    (fun i ↦ minusSourceIso X ≪≫ isoWhiskerRight (references (projection.app X) i)
      (sourceMap (minus.app X)).hom.toFunctor) = _
  rw [ModelSimplex.ofIsos_change_reference]
  exact (postcomp_ofIsos _ _ _ _).symm

/-- The middle family retains its original reference unchanged. -/
theorem middle_family :
    ModelSimplex.ofIsos (source X) (fun i ↦ (middleNodes X i).1)
      (fun i ↦ (middleNodes X i).2) = middleSimplex X := rfl


end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityTopNodes
