/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.WholePolynomialEndpointPushforward
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.GraphExterior.Linear
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut.ConstantUnit
public import Colib.AlgebraicGeometry.Correspondences.Graph.TargetPushforward
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.Normalization

/-!
# The power cut of the actual reduced exterior identity

The first summand recovers the original signed correspondence. Each
nonzero support of the constant term factors through the literal closed
unit section, so its two equations agree. The signed difference therefore
recovers the correspondence in the original power-cut domain.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction PresheafWithTransfers

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₖ" => multiplicativeGroupObject Sₖ
local notation "F" => parameterProduct Gₖ
local notation "γ" => CategoryTheory.Functor.map (graphFunctor k)

variable (X Y : SmoothSite (Spec (CommRingCat.of k)))

local notation "XG" => SmoothSite.product X Gₖ
local notation "YG" => SmoothSite.product Y Gₖ
set_option quotPrecheck false in
local notation "uY" => (unitSection.app Y)

private theorem unitSection_isClosedImmersion :
    IsClosedImmersion (uY).left := by
  let p := (productFst Y Gₖ).left
  let : IsSeparated p := inferInstanceAs (IsSeparated (pullback.fst Y.hom (Gₖ).hom))
  have hp : (uY).left ≫ p = 𝟙 Y.left :=
    congrArg (fun f => f.left) (unitSection_projection Y)
  let : IsClosedImmersion ((uY).left ≫ p) :=
    hp.symm ▸ MorphismProperty.id_mem @IsClosedImmersion Y.left
  exact IsClosedImmersion.of_comp (uY).left p

/-- Every nonzero original prime after postcomposition by the unit graph
has its entire target leg factoring through the actual unit section. -/
theorem torusPowerCutTarget_of_comp_unit_support
    (β : Cor.mk XG ⟶ Cor.mk Y) (z : torusPowerCutAmbient k X Y)
    (hz : (β ≫ γ uY).val z ≠ 0) :
    ∃ q : (integralComponentAt (X := torusPowerCutAmbient k X Y) z).subscheme ⟶ Y.left,
      torusPowerCutTarget k X Y z = q ≫ (uY).left := by
  let : IsClosedImmersion (uY).left := unitSection_isClosedImmersion k Y
  let m := graphTargetMap k XG uY
  let : IsClosedImmersion m := inferInstanceAs (IsClosedImmersion (graphTargetMap k XG uY))
  rw [comp_graph_val_of_finite k uY β] at hz
  obtain ⟨w, _, hw⟩ := finiteCyclePushforward_support_subset m β.val hz
  subst z
  let e := integralComponentMap m w
  let : IsIso e := AlgebraicCycle.integralComponentMap_isIso_of_isClosedImmersion m w
  let q := inv e ≫ (integralComponentAt w).subschemeι ≫ pullback.snd (XG).hom Y.hom
  refine ⟨q, ?_⟩
  have he := integralComponentMap_subschemeι m w
  change (integralComponentAt (m w)).subschemeι ≫ pullback.snd (XG).hom (YG).hom =
    (inv e ≫ (integralComponentAt w).subschemeι ≫ pullback.snd (XG).hom Y.hom) ≫ (uY).left
  calc
    _ = inv e ≫ e ≫ (integralComponentAt (m w)).subschemeι ≫
        pullback.snd (XG).hom (YG).hom := by rw [IsIso.inv_hom_id_assoc]
    _ = inv e ≫ (integralComponentAt w).subschemeι ≫ m ≫
        pullback.snd (XG).hom (YG).hom := by
      rw [← Category.assoc e (integralComponentAt (m w)).subschemeι, he, Category.assoc]
    _ = _ := by
      have hm : m ≫ pullback.snd (XG).hom (YG).hom =
          pullback.snd (XG).hom Y.hom ≫ (uY).left := graphTargetMap_snd k XG uY
      rw [hm]
      simp only [Category.assoc]

/-- A signed cut whose nonzero supports all have unit target has zero image. -/
theorem torusPowerCut_eq_zero_of_targetUnits (n : ℕ)
    (a : torusPowerCutDomain k X Y n)
    (ha : ∀ z : torusPowerCutAmbient k X Y, a.val.val z ≠ 0 →
      torusSupportCoordinate k (X := Y) (torusPowerCutTarget k X Y z) = 1) :
    torusPowerCut k X Y n a = 0 := by
  classical
  change (∑ᶠ z, finiteCorrespondenceContribution (XG).hom (YG).hom
    (fun w _ => if hw : TorusPowerCutAdmissibleAt k X Y w n then
      torusPowerCutPrime k X Y w n hw else 0) a.val z) = 0
  apply finsum_eq_zero_of_forall_eq_zero
  intro z
  by_cases hz : a.val.val z = 0
  · rw [finiteCorrespondenceContribution]
    split
    · change a.val.val z • _ = 0
      rw [hz, zero_zsmul]
    · rfl
  · have hpt := a.val.property.2 z hz
    have hcut := (mem_torusPowerCutDomain_iff k X Y n a.val).mp a.property z hz
    rw [finiteCorrespondenceContribution, dite_eq_left hpt, dite_eq_left hcut]
    change a.val.val z • torusPowerCutPrime k X Y z n hcut = 0
    rw [torusPowerCutPrime_eq_zero_of_target_unit (k := k) X Y z n hcut (ha z hz), zsmul_zero]

/-- The cut of the actual exterior identity with its constant unit part
subtracted recovers the original signed correspondence. -/
theorem torusPowerCut_reducedExterior (n : ℕ) (hn : n ≠ 0)
    (W : Cor.mk X ⟶ Cor.mk Y)
    (h : (F).map W - (F).map W ≫ torusUnitProjector k (Cor.mk Y) ∈
      torusPowerCutDomain k X Y n) :
    torusPowerCut k X Y n
      ⟨(F).map W - (F).map W ≫ torusUnitProjector k (Cor.mk Y), h⟩ = W := by
  let I := nativeExteriorToTorusPowerCutDomain k X Y n hn W
  let w₁ : Cor.mk XG ⟶ Cor.mk YG := (F).map W
  let b : Cor.mk XG ⟶ Cor.mk YG := w₁ ≫ torusUnitProjector k (Cor.mk Y)
  have hD : w₁ - b ∈ torusPowerCutDomain k X Y n := h
  have hI : I.val = w₁ := nativeExteriorToTorusPowerCutDomain_val k X Y n hn W
  have hb : b ∈ torusPowerCutDomain k X Y n := by
    have he := (torusPowerCutDomain k X Y n).sub_mem I.property hD
    rw [hI, sub_sub_cancel] at he
    exact he
  let B : torusPowerCutDomain k X Y n := ⟨b, hb⟩
  let β : Cor.mk XG ⟶ Cor.mk Y := w₁ ≫ γ (productFst Y Gₖ)
  have hβ : b = β ≫ γ uY := by
    change (F).map W ≫ torusUnitProjector k (Cor.mk Y) =
      ((F).map W ≫ γ (productFst Y Gₖ)) ≫ γ uY
    rw [torusUnitProjector_eq_graph, Functor.map_comp, Category.assoc]
  have hz : torusPowerCut k X Y n B = 0 := by
    apply torusPowerCut_eq_zero_of_targetUnits
    intro z hz
    change b.val z ≠ 0 at hz
    rw [hβ] at hz
    obtain ⟨q, hq⟩ := torusPowerCutTarget_of_comp_unit_support k X Y β z hz
    exact torusSupportCoordinate_eq_one_of_factor_unit q _ hq
  have he : (⟨w₁ - b, hD⟩ : torusPowerCutDomain k X Y n) = I - B := by
    apply Subtype.ext
    change w₁ - b = I.val - b
    rw [hI]
  change torusPowerCut k X Y n ⟨w₁ - b, hD⟩ = W
  rw [he, map_sub, torusPowerCut_nativeExteriorToTorusPowerCutDomain, hz, sub_zero]

end AlgebraicGeometry.Cor
