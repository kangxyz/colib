/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Representable
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.UnitSplit
import Colib.AlgebraicGeometry.Correspondences.BaseChange.IntegralSource
import Colib.AlgebraicGeometry.Correspondences.Coproducts.PartialIdentity
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.HomotopyInvariance
import Colib.AlgebraicGeometry.Sites.Smooth.NormalComponents

/-!
# Affine and torus sections of the base transfer representable

The actual structure graph freely generates correspondences from an integral
smooth scheme to the base. The diagonal of an arbitrary smooth scheme is a
sum of graphs supported on its clopen integral components. The additive
parameter product transports this decomposition to the cylinder. The affine
and torus projections therefore induce isomorphisms on base coefficients.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Chow TopologicalSpace
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction

universe u v w

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "B" => base S
set_option quotPrecheck false in
local notation "P₀" => (representableLarge k).obj (Cor.mk B)
set_option quotPrecheck false in
local notation "Γ" => (Cor.graphFunctor k).map

private def integralComponent (X : SmoothSite S) (t : genericPoints X.left) : SmoothSite S := by
  let U := componentOpen k X _ t.property
  let : NoetherianSpace U.toScheme := by
    change NoetherianSpace (U : Set X.left)
    infer_instance
  exact SmoothSite.mk (U.ι ≫ X.hom)

private instance integralComponent_isIntegral (X : SmoothSite S) (t : genericPoints X.left) :
    IsIntegral (integralComponent k X t).left :=
  isIntegral_componentOpen k X _ t.property

private def componentInclusion (X : SmoothSite S) (t : genericPoints X.left) :
    integralComponent k X t ⟶ X :=
  homMk (componentOpen k X _ t.property).ι rfl

private instance componentInclusion_isOpenImmersion
    (X : SmoothSite S) (t : genericPoints X.left) :
    IsOpenImmersion (componentInclusion k X t).left := by
  change IsOpenImmersion (componentOpen k X _ t.property).ι
  infer_instance

private theorem diagonalPrime_factors (X : SmoothSite S) (t : genericPoints X.left) :
    ∃ p : Cor.mk X ⟶ Cor.mk (integralComponent k X t),
      p ≫ Γ (componentInclusion k X t) = Cor.diagonalPrime k X t := by
  unfold Cor.diagonalPrime
  apply Cor.exists_graph_factorization_of_range_subset
  have hd := integralComponentAt_graphMap_snd X.hom X.hom (𝟙 X.left)
    (Category.id_comp _) t.val
  have h := hd.trans ((Category.assoc _ _ _).symm.trans (Category.comp_id _))
  rw [h, range_integralComponentAt_graphMap_fst]
  change closure {t.val} ⊆ Set.range (componentOpen k X _ t.property).ι
  simpa only [Scheme.Opens.range_ι, coe_componentOpen] using
    (Set.Subset.rfl : closure {t.val} ⊆ closure {t.val})

private theorem hom_ext_of_component_graph {C : Type v} [Category.{w} C] [Preadditive C]
    (F : Cor k ⥤ C) [F.Additive] (X : SmoothSite S)
    {Y : C} {a b : F.obj (Cor.mk X) ⟶ Y}
    (h : ∀ t : genericPoints X.left,
      F.map (Γ (componentInclusion k X t)) ≫ a = F.map (Γ (componentInclusion k X t)) ≫ b) :
    a = b := by
  classical
  let := (Cor.finite_genericPoints k (Cor.mk X)).fintype
  have hId : 𝟙 (F.obj (Cor.mk X)) = ∑ t : genericPoints X.left,
      F.map (Cor.diagonalPrime k X t) := by
    rw [← F.map_id, Cor.identity_eq_sum_diagonalPrime, F.map_sum]
  calc
    a = ∑ t : genericPoints X.left, F.map (Cor.diagonalPrime k X t) ≫ a := by
      rw [← Preadditive.sum_comp, ← hId, Category.id_comp]
    _ = ∑ t : genericPoints X.left, F.map (Cor.diagonalPrime k X t) ≫ b := by
      apply Finset.sum_congr rfl
      intro t _
      obtain ⟨p, hp⟩ := diagonalPrime_factors k X t
      simp only [← hp, F.map_comp, Category.assoc, h t]
    _ = b := by rw [← Preadditive.sum_comp, ← hId, Category.id_comp]

local instance (Y : SmoothSite S) [IsIntegral Y.left] :
    IsIntegral ((𝟭 Scheme).obj Y.left) := inferInstanceAs (IsIntegral Y.left)

private theorem eq_zsmul_toBaseGraph {Y : SmoothSite S} [IsIntegral Y.left]
    (a : Cor.mk Y ⟶ Cor.mk B) :
    a = structureCorrespondenceCoeff Y.hom a • Γ (toBase Y) :=
  (eq_coeff_zsmul_structureGraph Y.hom a).trans
    (congrArg (structureCorrespondenceCoeff Y.hom a • ·)
      (graphCorrespondenceOfComponents_structure Y.hom
        (Cor.finite_genericPoints k (Cor.mk Y))).symm)

private theorem graph_comp_base_of_integral {X Y : SmoothSite S} [IsIntegral Y.left]
    (f : X ⟶ Y) (a : Cor.mk Y ⟶ Cor.mk B) :
    Γ f ≫ a = structureCorrespondenceCoeff Y.hom a • Γ (toBase X) := by
  calc
    Γ f ≫ a = Γ f ≫ (structureCorrespondenceCoeff Y.hom a • Γ (toBase Y)) :=
      congrArg (Γ f ≫ ·) (eq_zsmul_toBaseGraph k a)
    _ = _ := by rw [Preadditive.comp_zsmul, ← Functor.map_comp, comp_toBase]

/-- For a pointed geometrically integral parameter, the original transfer
representable of the base inverts pullback along the parameter projection. -/
theorem isIso_baseRepresentable_projection
    (T : SmoothSite S) [GeometricallyIntegral T.hom] (t : B ⟶ T) (X : SmoothSite S) :
    IsIso (transfer P₀ (Γ (productFst X T))) := by
  let p (U : SmoothSite S) := productFst U T
  let s (U : SmoothSite S) := productLift (𝟙 U) (toBase U ≫ t)
  have hs {U V : SmoothSite S} (f : U ⟶ V) :
      f ≫ s V = s U ≫ SmoothSite.productMap f (𝟙 T) := by
    apply product_hom_ext <;> simp [s, Category.assoc]
  refine ⟨⟨transfer P₀ (Γ (s X)), ?_, ?_⟩⟩
  · have h : s X ≫ p X = 𝟙 X := productLift_fst _ _
    rw [← transfer_comp, ← Functor.map_comp, h, (Cor.graphFunctor k).map_id X]
    exact transfer_id P₀ (Cor.mk X)
  · apply AddCommGrpCat.ext
    intro x
    change ULift.up (Γ (p X) ≫ Γ (s X) ≫ x.down) = x
    apply ULift.ext
    change Γ (p X) ≫ Γ (s X) ≫ x.down = x.down
    apply hom_ext_of_component_graph k (Cor.parameterProduct T) X
    intro i
    rw [Cor.parameterProduct_graph]
    let U := integralComponent k X i
    let q := componentInclusion k X i
    let r := SmoothSite.productMap q (𝟙 T)
    let : IsIntegral U.left := integralComponent_isIntegral k X i
    let : IsLocallyNoetherian ((𝟭 Scheme).obj U.left) :=
      SmoothSite.isLocallyNoetherian_overField k U
    let : IsIntegral (product U T).left := by
      change IsIntegral (pullback U.hom T.hom)
      exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst U.hom T.hom)
    change Γ r ≫ Γ (p X) ≫ Γ (s X) ≫ x.down = Γ r ≫ x.down
    have h : (r ≫ p X) ≫ s X = (p U ≫ s U) ≫ r := by
      have hr : r ≫ p X = p U ≫ q := productMap_fst _ _
      rw [hr, Category.assoc, hs, ← Category.assoc]
    calc
      _ = Γ ((r ≫ p X) ≫ s X) ≫ x.down := by
        simp only [Functor.map_comp, Category.assoc]
      _ = Γ (p U ≫ s U) ≫ (Γ r ≫ x.down) := by
        rw [h, Functor.map_comp, Category.assoc]
      _ = _ := by
        rw [graph_comp_base_of_integral]
        exact (eq_zsmul_toBaseGraph k (Γ r ≫ x.down)).symm

/-- The original presheaf of correspondences to the base is homotopy invariant. -/
theorem baseRepresentable_isA1Invariant : IsA1Invariant P₀ := by
  intro X
  rw [a1ProjectionPullback_eq_transfer]
  exact isIso_baseRepresentable_projection k _ (torusOne S ≫ multiplicativeGroupOpen S) X

/-- Constant sections identify the original base coefficient with its torus
sections in the native base-product coordinates. -/
theorem isIso_torusConstant_baseRepresentable : IsIso (torusConstant P₀) := by
  apply (ObjectProperty.isIso_hom_iff _).mp
  have (X : (Cor k)ᵒᵖ) : IsIso ((torusConstant P₀).hom.app X) := by
    let e := (SheafWithTransfers.baseSectionsPresheafIso k P₀).hom.hom.app X
    let : IsIso e := inferInstanceAs (IsIso
      ((SheafWithTransfers.baseSectionsPresheafIso k P₀).hom.hom.app X))
    have : IsIso (e ≫ (torusConstant P₀).hom.app X) := by
      change IsIso (transfer P₀ (Γ (productBaseIso X.unop.toSmoothSite).hom) ≫
        transfer P₀ (Γ (SmoothSite.productMap (𝟙 X.unop.toSmoothSite) (toBase
          (multiplicativeGroupObject S)))))
      rw [← transfer_comp, ← Functor.map_comp, productMap_toBase]
      exact isIso_baseRepresentable_projection k _ (torusOne S) X.unop.toSmoothSite
    exact IsIso.of_isIso_comp_left e _
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.PresheafWithTransfers

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "B" => base S
set_option quotPrecheck false in
local notation "P₀" => (representableLarge k).obj (Cor.mk B)
set_option quotPrecheck false in
local notation "F₀" => (transferRepresentable k).obj (Cor.mk B)

/-- The genuine Nisnevich sheafification of the base representable is
homotopy invariant. -/
theorem baseTransferRepresentable_isA1Invariant : IsA1Invariant (F₀).obj :=
  nisnevichSheafify_isA1Invariant P₀ (baseRepresentable_isA1Invariant k)

/-- The constant sections of the actual base transfer sheaf induce an
isomorphism onto its torus sections. -/
theorem isIso_torusSectionsConstant_baseTransferRepresentable :
    IsIso ((torusSectionsConstantNatTrans k).app F₀) := by
  let A := nisnevichSheafify k
  let G := multiplicativeGroupObject S
  let : IsIso (torusConstant P₀) := isIso_torusConstant_baseRepresentable k
  let : IsIso (torusSectionsSheafificationComparison k P₀) :=
    isIso_torusSectionsSheafificationComparison k P₀ (baseRepresentable_isA1Invariant k)
  have h : A.map (torusConstant P₀) ≫ torusSectionsSheafificationComparison k P₀ =
      parameterSectionsSheafificationComparison k B P₀ ≫
        (parameterSectionsPullbackNatTrans k (toBase G)).app F₀ :=
    parameterSectionsSheafificationComparison_parameterMap k (toBase G) P₀
  have hc : A.map ((baseSectionsPresheafIso k P₀).hom ≫ torusConstant P₀) ≫
      torusSectionsSheafificationComparison k P₀ =
        (torusSectionsConstantNatTrans k).app F₀ := by
    rw [Functor.map_comp, Category.assoc, h, ← Category.assoc, baseSectionsSheafification_hom]
    change _ ≫ _ = (_ ≫ _) ≫ 𝟙 _
    rw [Category.comp_id]
    rfl
  rw [← hc]
  infer_instance

end AlgebraicGeometry.SheafWithTransfers
