/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PrincipalFamilyEndpoint
public import Colib.AlgebraicGeometry.Correspondences.Moving.Polynomial.PrincipalFamilySupport
public import Colib.AlgebraicGeometry.Correspondences.Moving.Polynomial.RetainedGraph
public import Colib.AlgebraicGeometry.Correspondences.Moving.PrincipalOrderOpenPushforward

/-! # The actual homotopy of a principal correspondence

The interpolating family is first read in the product with the retained
curve itself. This graph keeps the whole signed fibers, and graph
postcomposition preserves the original residue degrees.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor.PrincipalOrder

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.PolynomialSectionPencil
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction
open _root_.AlgebraicGeometry.AlgebraicCycle
open _root_.AlgebraicGeometry.PrincipalFamilyUnitOpen hiding
  parameterSpace projection parameter endpoint

/-- The actual canonical open contains the whole original omitted locus. -/
theorem canonical_boundary_cover {C V B : Scheme.{u}} (j : V ⟶ C) (W : C.Opens)
    (b : B ⟶ W.toScheme) (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ W.ι)) :
    (Set.range j)ᶜ ⊆ (W : Set C) := by
  intro x hx
  obtain ⟨z, hz⟩ := hcover hx
  rw [← hz]
  exact (b z).property

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k))) [IsAffine X.left]
  [IsIntegral X.left] {C V B : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
  [IsIntegral V] [IsNoetherian V] [V.IsQuasiAffine]
  (q : C ⟶ X.left) [IsProper q] (j : V ⟶ C) [IsOpenImmersion j]
  [SmoothOfRelativeDimension 1 (j ≫ q)]
  (W : C.Opens) (r : Γ(C, W)) (b : B ⟶ W.toScheme) [Nonempty B]
  (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ W.ι)) (hb : b.appTop (W.topIso.inv r) = 1)

set_option quotPrecheck false in
local notation "t" => (q ≫ X.hom)
set_option quotPrecheck false in
local notation "U" => ambientUnitOpen (q ≫ X.hom) W.ι (W.topIso.inv r)
local notation "L" => SmoothSite.product X (polynomialAffineLine (CommRingCat.of k))

include hcover hb in
omit [IsIntegral X.left] [Nonempty B] in
/-- The interpolating divisor gives its native correspondence on the retained graph. -/
theorem exists_familyCorrespondence_with_retained_value [Nonempty U] :
    ∃ α : Cor.mk L ⟶ Cor.mk (retainedSite X q j), α.val =
      finiteCyclePushforward (retainedFamilyGraph X q j)
        (retainedFamilyCycle t W.ι (W.topIso.inv r) j) := by
  let q' : parameterSpace t ⟶ (L).left := parameterMap X.hom q
  let j' := parameterMap t j
  let g' := projection (j ≫ t) ≫ 𝟙 V
  let : IsProper q' := MorphismProperty.of_isPullback
    (parameterMap_isPullback X.hom q) inferInstance
  let : IsAffine (L).left :=
    isAffine_of_isAffineHom (X := parameterSpace X.hom) (Y := X.left) (projection X.hom)
  let : (parameterSpace (j ≫ t)).IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_isAffineHom (projection (j ≫ t))
  let : IsOpenImmersion j' := inferInstanceAs (IsOpenImmersion (parameterMap t j))
  let : SmoothOfRelativeDimension 1 (j' ≫ q') := by
    change SmoothOfRelativeDimension 1 (parameterMap t j ≫ parameterMap X.hom q)
    rw [parameterMap_comp]
    exact (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (parameterMap_isPullback X.hom (j ≫ q)) inferInstance
  let s := ambientUnitSection t W.ι (W.topIso.inv r)
  have hU := complement_subset_ambientUnitOpen t j W.ι b hcover (W.topIso.inv r) hb
  rw [lineMap_eq_parameterMap] at hU
  let hs := isUnit_ambientUnitSection t W.ι (W.topIso.inv r)
  have hg : j' ≫ q' ≫ (L).hom = g' ≫ (retainedSite X q j).hom := by
    change parameterMap t j ≫ parameterMap X.hom q ≫ projection X.hom ≫ X.hom =
      (projection (j ≫ t) ≫ 𝟙 V) ≫ (j ≫ q ≫ X.hom)
    simp only [Category.assoc, parameterMap_projection_assoc, Category.id_comp]
  exact exists_correspondence_with_closed_value q' j' U hU s hs g' hg
    (retainedFamilyGraph X q j) (retainedFamilyGraph_fst X q j)
    ((retainedFamilyGraph_snd X q j).trans (Category.comp_id _).symm)

variable [Nonempty W] (hr : IsUnit r)

set_option quotPrecheck false in
local notation "β" => correspondence q j W (canonical_boundary_cover j W b hcover)
  r hr (𝟙 V) (retainedIdentityBase X q j)

include hb in
/-- The closed-graph principal family has the zero correspondence at zero
and the original principal correspondence at one. -/
theorem exists_familyCorrespondence_retained_endpoints :
    ∃ α : Cor.mk L ⟶ Cor.mk (retainedSite X q j),
      (graphFunctor k).map (polynomialAffineSection (.of k) X 0) ≫ α = 0 ∧
        (graphFunctor k).map (polynomialAffineSection (.of k) X 1) ≫ α = β := by
  let f := W.topIso.inv r
  let : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  let : Nonempty U := nonempty_ambientUnitOpen_of_boundary t W.ι b f hb
  obtain ⟨α, hα⟩ := exists_familyCorrespondence_with_retained_value X q j W r b hcover hb
  let : Nonempty (unitOpen (W.ι ≫ t) f) := by
    obtain ⟨z⟩ : Nonempty U := inferInstance
    obtain ⟨y, hy, _⟩ := (show z.val ∈ (parameterMap t W.ι) ''ᵁ unitOpen (W.ι ≫ t) f
      from by simpa only [ambientUnitOpen, lineMap_eq_parameterMap] using z.property)
    exact ⟨⟨y, hy⟩⟩
  let : Nonempty (⊤ : W.toScheme.Opens) :=
    ⟨⟨genericPoint W.toScheme, TopologicalSpace.Opens.mem_top _⟩⟩
  have hf : f ≠ 0 := (hr.map W.topIso.inv.hom).ne_zero
  have hflat (z : parameterSpace t) (hz : originalOrderCycle t W.ι f z ≠ 0) :
      Flat ((integralComponentAt z).subschemeι ≫ parameterProjection t) :=
    familySupport_parameterFlat X q j W r b hcover hb z hz
  have hends := retainedFamilyCycle_endpoints t W.ι f j hf hflat
  let : IsDominant j :=
    ((tfae_isDominant_of_isIntegral j).out 1 2).mpr (genericPoint_eq_of_isOpenImmersion j)
  have hβ : (β).val =
      finiteCyclePushforward (retainedGraph X q j) (retainedOrderCycle W.ι f j) := by
    have he := correspondence_val_eq_pushforward_of_closed q j W
      (canonical_boundary_cover j W b hcover) r hr (𝟙 V) (retainedIdentityBase X q j)
      (retainedGraph X q j) (retainedGraph_fst X q j) (retainedGraph_snd X q j)
    have hgerm : openSectionGerm W.ι f = C.germToFunctionField W r :=
      openSectionGerm_topIso W r
    exact he.trans (congrArg (fun g : C.functionField =>
      finiteCyclePushforward (retainedGraph X q j) (principalCycle V
        (dominantFunctionFieldMap j g))) hgerm.symm)
  have hgraph (a : k) :=
    graph_comp_closedCycle_endpoint_of_parameter_eq (polynomialAffineSection (.of k) X a)
      (parameterProjection X.hom) a (polynomialAffineSection_isPullback X a)
      (retainedFamilyGraph X q j) (parameterProjection (j ≫ t))
      (retainedFamilyGraph_parameter X q j) (retainedFamilyCycle t W.ι f j) α
      hα
  refine ⟨α, ?_, ?_⟩
  · apply Subtype.ext
    change _ = (0 : AlgebraicCycle (pullback X.hom (retainedSite X q j).hom) ℤ)
    simpa only [hends.1, map_zero] using hgraph 0
  · apply Subtype.ext
    rw [hgraph 1, hends.2, finiteCyclePushforward_comp_apply, hβ]
    exact DFunLike.congr_fun
      (finiteCyclePushforward_congr _ _ (retainedFamilyGraph_endpoint X q j 1)) _

end AlgebraicGeometry.Cor.PrincipalOrder
