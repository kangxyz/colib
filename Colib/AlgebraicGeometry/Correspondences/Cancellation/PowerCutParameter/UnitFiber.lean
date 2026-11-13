/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry

/-!
# The unit fibre of the Laurent parameter graph

The fibre of the graph parameter `a * u⁻¹` at the literal unit section is
the whole zero scheme of `a - u`. The Cartesian square retains both the
inclusion into the original support and its map to the original base.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction

variable (k : Type u) [Field k] {X : SmoothSite (Spec (.of k))} {P : Scheme.{u}}
  (g : P ⟶ (SmoothSite.product X
    (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).left)

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => multiplicativeGroupObject Sₖ
local notation "T" => (product X Gₘ)

private theorem unitSection_left_fst :
    (unitSection.app X).left ≫ (productFst X Gₘ).left = 𝟙 X.left :=
  congrArg (fun φ => φ.left) (unitSection_projection X)

private theorem unitSection_left_snd :
    (unitSection.app X).left ≫ (productSnd X Gₘ).left = (nativeTorusPoint X.hom 1).left := by
  have h := congrArg (fun φ => φ.left) (productLift_snd (𝟙 X) (toBase X ≫ torusOne Sₖ))
  change (unitSection.app X).left ≫ (productSnd X Gₘ).left =
    X.hom ≫ (nativeTorusPoint (𝟙 Sₖ) 1).left at h
  exact h.trans (nativeTorusPoint_one X.hom).symm

set_option quotPrecheck false in
local notation "b" => (g ≫ (T).hom)
set_option quotPrecheck false in
local notation "p" => torusSupportBaseProjection k g
set_option quotPrecheck false in
local notation "Aₚ" => Γ(P, ⊤)

private theorem map_unit_eq_of_nativeTorusPoint_comp_eq {A B D : Scheme.{u}}
    (f : A ⟶ Sₖ) (g' : B ⟶ Sₖ) (i : D ⟶ A) (j : D ⟶ B)
    (u : (Γ(A, ⊤))ˣ) (v : (Γ(B, ⊤))ˣ)
    (h : i ≫ (nativeTorusPoint f u).left = j ≫ (nativeTorusPoint g' v).left) :
    Units.map i.appTop.hom.toMonoidHom u = Units.map j.appTop.hom.toMonoidHom v := by
  have hi := nativeTorusPoint_comp_left f i u
  have hj := nativeTorusPoint_comp_left g' j v
  let coordinate (m : D ⟶ multiplicativeGroupBaseChange Sₖ) :=
    Units.map m.appTop.hom.toMonoidHom (multiplicativeGroupBaseChangeCoordinate Sₖ)
  have he := congrArg coordinate (hi.trans (h.trans hj.symm))
  exact (nativeTorusPoint_coordinate (i ≫ f) (Units.map i.appTop.hom.toMonoidHom u)).symm.trans
    (he.trans (nativeTorusPoint_coordinate (j ≫ g') (Units.map j.appTop.hom.toMonoidHom v)))

private theorem map_unit_quotient_eq_one_iff {A D : Scheme.{u}} (i : D ⟶ A)
    (a u₀ : (Γ(A, ⊤))ˣ) :
    Units.map i.appTop.hom.toMonoidHom (a * u₀⁻¹) = 1 ↔
      i.appTop (a.val - u₀.val) = 0 := by
  rw [map_mul, map_inv, mul_inv_eq_one, map_sub, sub_eq_zero]
  constructor
  · exact congrArg Units.val
  · intro h
    apply Units.ext
    exact h

/-- The actual zero scheme of `a - u` is the pullback of the parameter projection
for `a * u⁻¹` along the native unit section of the source torus. -/
theorem isPullback_torusPowerCutParameterProjection_unitSection (a u₀ : Aₚˣ) :
    IsPullback
      (AffineLineFiber.inclusion (sectionToAffineLine b (a.val - u₀.val)) 0)
      (AffineLineFiber.inclusion (sectionToAffineLine b (a.val - u₀.val)) 0 ≫ p)
      (torusPowerCutParameterProjection k g (a * u₀⁻¹)) (unitSection.app X).left := by
  let s := a.val - u₀.val
  let F := sectionToAffineLine b s
  let i := AffineLineFiber.inclusion F 0
  let v := torusPowerCutParameterProjection k g (a * u₀⁻¹)
  let e := (unitSection.app X).left
  have hratio : Units.map i.appTop.hom.toMonoidHom (a * u₀⁻¹) = 1 :=
    (map_unit_quotient_eq_one_iff i a u₀).mpr (section_zero_inclusion_appTop b s)
  have hb : (i ≫ p) ≫ X.hom = i ≫ b := by
    change (i ≫ g ≫ (productFst X Gₘ).left) ≫ X.hom =
      i ≫ g ≫ (productFst X Gₘ).left ≫ X.hom
    simp only [Category.assoc]
  have ht : i ≫ (nativeTorusPoint b (a * u₀⁻¹)).left =
      (i ≫ p) ≫ (nativeTorusPoint X.hom 1).left := by
    rw [← nativeTorusPoint_comp_left b i, ← nativeTorusPoint_comp_left X.hom (i ≫ p),
      hratio, map_one, hb]
  have hcomm : i ≫ v = (i ≫ p) ≫ e := by
    apply pullback.hom_ext
    · change (i ≫ v) ≫ (productFst X Gₘ).left = ((i ≫ p) ≫ e) ≫ (productFst X Gₘ).left
      simp only [v, e, Category.assoc, torusPowerCutParameterProjection_fst,
        unitSection_left_fst, Category.comp_id]
    · change (i ≫ v) ≫ (productSnd X Gₘ).left = ((i ≫ p) ≫ e) ≫ (productSnd X Gₘ).left
      simp only [v, e, Category.assoc, torusPowerCutParameterProjection_snd, unitSection_left_snd]
      exact Category.assoc i p _ ▸ ht
  refine IsPullback.of_isLimit' ⟨hcomm⟩ (PullbackCone.isLimitAux' _ (fun c => ?_))
  have hX : c.fst ≫ p = c.snd := by
    have h := congrArg (fun m => m ≫ (productFst X Gₘ).left) c.condition
    simpa only [v, e, Category.assoc, torusPowerCutParameterProjection_fst,
      unitSection_left_fst, Category.comp_id] using h
  have hG : c.fst ≫ (nativeTorusPoint b (a * u₀⁻¹)).left =
      c.snd ≫ (nativeTorusPoint X.hom 1).left := by
    have h := congrArg (fun m => m ≫ (productSnd X Gₘ).left) c.condition
    simpa only [v, e, Category.assoc, torusPowerCutParameterProjection_snd,
      unitSection_left_snd] using h
  have hW : Units.map c.fst.appTop.hom.toMonoidHom (a * u₀⁻¹) = 1 := by
    have h := map_unit_eq_of_nativeTorusPoint_comp_eq k b X.hom c.fst c.snd (a * u₀⁻¹) 1 hG
    rwa [map_one] at h
  have hzero : c.fst.appTop s = 0 := (map_unit_quotient_eq_one_iff c.fst a u₀).mp hW
  have hF : c.fst ≫ F = (c.fst ≫ b) ≫ AffineLineFiber.point 0 := by
    rw [← sectionToAffineLine_comp c.fst b, hzero, sectionToAffineLine_zero]
  let m := pullback.lift (c.fst ≫ b) c.fst hF.symm
  have hm : m ≫ i = c.fst := pullback.lift_snd _ _ _
  refine ⟨m, hm, ?_, ?_⟩
  · change m ≫ (i ≫ p) = c.snd
    rw [← Category.assoc, hm, hX]
  · intro n hn _
    apply (cancel_mono i).mp
    exact hn.trans hm.symm

end AlgebraicGeometry.Cor
