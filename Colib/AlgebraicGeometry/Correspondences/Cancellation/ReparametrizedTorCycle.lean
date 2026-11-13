/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.ReparametrizedTor
public import Colib.AlgebraicGeometry.Correspondences.Composition.TorCycle
import Colib.AlgebraicGeometry.Chow.WholePolynomialEndpointPushforward
import StacksFrontier.AlgebraicGeometry.Divisors.Relative.SmoothSection
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.PerfectFactor

/-!
# The exact signed Tor cycle is independent of the parameter presentation

Two choices of parameter on the same right support give the same native
Tor coefficients at the points of their common incidence. After comparing
the actual outer maps, their finite pushforwards give the exact cycle
identity, including residue degrees.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace RingTheory.Sequence
open AlgebraicGeometry.Scheme AlgebraicCycle

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "T" => SmoothSite.multiplicativeGroupObject Sₖ

variable (U X Z₁ Z₂ : SmoothSite (Spec (.of k)))

local notation3 (prettyPrint := false) "f" => (SmoothSite.product U T).hom
local notation3 (prettyPrint := false) "g" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "h₁" => (SmoothSite.product Z₁ T).hom
local notation3 (prettyPrint := false) "h₂" => (SmoothSite.product Z₂ T).hom

variable (z : pullback (C := Scheme)
    (SmoothSite.product U (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom
    (SmoothSite.product X (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom)
  (w₁ : pullback (C := Scheme)
    (SmoothSite.product X (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom
    (SmoothSite.product Z₁ (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom)
  (w₂ : pullback (C := Scheme)
    (SmoothSite.product X (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom
    (SmoothSite.product Z₂ (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom)
  {Q P : Scheme.{u}} (p : Q ⟶ X.left) (r : P ⟶ X.left)
  (l₁ l₂ : P ⟶ (SmoothSite.multiplicativeGroupObject (Spec (.of k))).left)
  (hl₁ : r ≫ X.hom = l₁ ≫ (SmoothSite.multiplicativeGroupObject (Spec (.of k))).hom)
  (hl₂ : r ≫ X.hom = l₂ ≫ (SmoothSite.multiplicativeGroupObject (Spec (.of k))).hom)
  (eQ : pullback (C := Scheme) (p ≫ X.hom)
    (SmoothSite.multiplicativeGroupObject (Spec (.of k))).hom ≅ (integralComponentAt z).subscheme)
  (eP₁ : P ≅ (integralComponentAt w₁).subscheme)
  (eP₂ : P ≅ (integralComponentAt w₂).subscheme)
  (hQ : eQ.hom ≫ ((integralComponentAt z).subschemeι ≫ pullback.snd
    (SmoothSite.product U (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom
    (SmoothSite.product X (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom) =
    pullbackParameterExtensionMap p X.hom
      (SmoothSite.multiplicativeGroupObject (Spec (.of k))).hom)
  (hP₁ : eP₁.hom ≫ ((integralComponentAt w₁).subschemeι ≫ pullback.fst
    (SmoothSite.product X (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom
    (SmoothSite.product Z₁ (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom) =
    pullback.lift r l₁ hl₁)
  (hP₂ : eP₂.hom ≫ ((integralComponentAt w₂).subschemeι ≫ pullback.fst
    (SmoothSite.product X (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom
    (SmoothSite.product Z₂ (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom) =
    pullback.lift r l₂ hl₂)

local notation3 (prettyPrint := false) "I₁" => correspondenceIncidence f g h₁ z w₁
local notation3 (prettyPrint := false) "I₂" => correspondenceIncidence f g h₂ z w₂
local notation3 (prettyPrint := false) "e₁" =>
  (@reparametrizedIncidenceIso k _ U X Z₁ T z w₁ Q P p r l₁ hl₁ eQ eP₁ hQ hP₁ :
    pullback (C := Scheme) p r ≅ I₁)
local notation3 (prettyPrint := false) "e₂" =>
  (@reparametrizedIncidenceIso k _ U X Z₂ T z w₂ Q P p r l₂ hl₂ eQ eP₂ hQ hP₂ :
    pullback (C := Scheme) p r ≅ I₂)

set_option maxHeartbeats 240000 in
-- The coefficient comparison retains both literal incidence presentations.
/-- The alternating Tor coefficient agrees at the same original generic
incidence point for both parameter maps. -/
theorem reparametrizedIncidenceTorCoefficient_eq
    (x : genericPoints (pullback (C := Scheme) p r)) :
    correspondenceIncidenceTorCoefficient k f g h₁ z w₁
      ⟨(e₁).hom x.val, mem_genericPoints_of_flat (e₁).hom x.property⟩ =
    correspondenceIncidenceTorCoefficient k f g h₂ z w₂
      ⟨(e₂).hom x.val, mem_genericPoints_of_flat (e₂).hom x.property⟩ := by
  let x₁ : genericPoints I₁ := ⟨(e₁).hom x.val, mem_genericPoints_of_flat (e₁).hom x.property⟩
  let x₂ : genericPoints I₂ := ⟨(e₂).hom x.val, mem_genericPoints_of_flat (e₂).hom x.property⟩
  let xₘ := reparametrizedRemainingMiddlePair X p r (reparametrizedIncidenceToProduct X p r x.val)
  let x₀ := p (pullback.fst p r x.val)
  let δ := pullback.diagonal X.hom
  have hxₘ : xₘ = δ x₀ := congrArg (fun u : pullback p r ⟶ pullback X.hom X.hom => u x.val)
    (reparametrizedIncidenceToProduct_middleDiagonal X p r)
  obtain ⟨s, hs, hk⟩ : ∃ s : List ((pullback X.hom X.hom).presheaf.stalk xₘ),
      IsRegular ((pullback X.hom X.hom).presheaf.stalk xₘ) s ∧
        Ideal.ofList s = IdealSheafData.stalk δ.ker xₘ := by
    rw [hxₘ]
    obtain ⟨s, hs, hk⟩ :=
      Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_isRegular_ker_stalkMap_of_isRegularImmersion
        δ (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section
          (pullback.fst X.hom X.hom) δ (pullback.diagonal_fst X.hom)) x₀
    exact ⟨s, hs, hk.trans (ker_stalkMap_eq_idealStalk_ker δ x₀)⟩
  let b₁ := correspondenceIncidenceTorDegreeBound k f g h₁ z w₁ x₁.val
  let b₂ := correspondenceIncidenceTorDegreeBound k f g h₂ z w₂ x₂.val
  let B := max b₁ b₂
  change correspondenceIncidenceTorCoefficient k f g h₁ z w₁ x₁ =
    correspondenceIncidenceTorCoefficient k f g h₂ z w₂ x₂
  rw [correspondenceIncidenceTorCoefficient_eq_sum_range k f g h₁ z w₁ x₁ B (le_max_left _ _),
    correspondenceIncidenceTorCoefficient_eq_sum_range k f g h₂ z w₂ x₂ B (le_max_right _ _)]
  apply Finset.sum_congr rfl
  intro n _
  have hlen := (reparametrizedIncidenceTor_length_eq_remainingKoszul U X Z₁ z w₁
    p r l₁ hl₁ eQ eP₁ hQ hP₁ x.val s hs hk n).trans
    (reparametrizedIncidenceTor_length_eq_remainingKoszul U X Z₂ z w₂
      p r l₂ hl₂ eQ eP₂ hQ hP₂ x.val s hs hk n).symm
  exact congrArg (fun m : ℕ∞ => (-1 : ℤ) ^ n * (m.toNat : ℤ)) hlen

local notation3 (prettyPrint := false) "e" => ((e₁).symm ≪≫ (e₂) : I₁ ≅ I₂)

set_option maxHeartbeats 240000 in
-- Both cycle evaluations are formed on the native generic-point subtypes.
/-- The signed native incidence cycles agree by the actual incidence isomorphism. -/
theorem reparametrizedIncidenceTorCycle_map
    (hw₁ : IsFiniteCorrespondencePoint g h₁ w₁) (hw₂ : IsFiniteCorrespondencePoint g h₂ w₂) :
    finiteCyclePushforward (e).hom (incidenceTorCycle f g h₁ z w₁ hw₁) =
      incidenceTorCycle f g h₂ z w₂ hw₂ := by
  apply Function.locallyFinsuppWithin.ext
  intro t
  obtain ⟨x, rfl⟩ := (e₂).hom.surjective t
  have hc : (e₁).hom ≫ (e).hom = (e₂).hom := by
    change (e₁).hom ≫ (e₁).inv ≫ (e₂).hom = (e₂).hom
    exact (e₁).hom_inv_id_assoc (e₂).hom
  have he : (e).hom ((e₁).hom x) = (e₂).hom x :=
    congrArg (fun v : pullback p r ⟶ I₂ => v x) hc
  have hval := finiteCyclePushforward_apply_of_isClosedImmersion
    (e).hom (incidenceTorCycle f g h₁ z w₁ hw₁) ((e₁).hom x)
  rw [he] at hval
  refine hval.trans ?_
  by_cases hx : x ∈ genericPoints (pullback (C := Scheme) p r)
  · rw [incidenceTorCycle_apply_generic f g h₁ z w₁ hw₁
      ⟨(e₁).hom x, mem_genericPoints_of_flat (e₁).hom hx⟩,
      incidenceTorCycle_apply_generic f g h₂ z w₂ hw₂
      ⟨(e₂).hom x, mem_genericPoints_of_flat (e₂).hom hx⟩]
    exact reparametrizedIncidenceTorCoefficient_eq U X Z₁ Z₂ z w₁ w₂
      p r l₁ l₂ hl₁ hl₂ eQ eP₁ eP₂ hQ hP₁ hP₂ ⟨x, hx⟩
  · have h₁' : (e₁).hom x ∉ genericPoints I₁ := fun h' => hx (by
      have hpoint : (e₁).inv ((e₁).hom x) = x :=
        (Scheme.Hom.comp_apply (e₁).hom (e₁).inv x).symm.trans
          (congrArg (fun m : pullback p r ⟶ pullback p r => m x) (e₁).hom_inv_id)
      exact hpoint ▸ mem_genericPoints_of_flat (e₁).inv h')
    have h₂' : (e₂).hom x ∉ genericPoints I₂ := fun h' => hx (by
      have hpoint : (e₂).inv ((e₂).hom x) = x :=
        (Scheme.Hom.comp_apply (e₂).hom (e₂).inv x).symm.trans
          (congrArg (fun m : pullback p r ⟶ pullback p r => m x) (e₂).hom_inv_id)
      exact hpoint ▸ mem_genericPoints_of_flat (e₂).inv h')
    rw [incidenceTorCycle_apply_of_notMem f g h₁ z w₁ hw₁ _ h₁',
      incidenceTorCycle_apply_of_notMem f g h₂ z w₂ hw₂ _ h₂']

set_option maxHeartbeats 240000 in
-- The comparison uses the actual proper maps from both full incidence schemes.
/-- The exact finite pushforward commutes with the two native incidences
when the actual outer maps agree after the given target map. -/
theorem reparametrizedIncidenceTorCorrespondence_val_map
    (hz : IsFiniteCorrespondencePoint f g z)
    (hw₁ : IsFiniteCorrespondencePoint g h₁ w₁) (hw₂ : IsFiniteCorrespondencePoint g h₂ w₂)
    (j : pullback (C := Scheme) f h₁ ⟶ pullback (C := Scheme) f h₂) [IsFinite j]
    (hj : (e₁).hom ≫ correspondenceIncidenceMap f g h₁ z w₁ ≫ j =
      (e₂).hom ≫ correspondenceIncidenceMap f g h₂ z w₂) :
    finiteCyclePushforward j (incidenceTorCorrespondence f g h₁ z w₁ hz hw₁).val =
      (incidenceTorCorrespondence f g h₂ z w₂ hz hw₂).val := by
  let F₁ := correspondenceIncidenceMap f g h₁ z w₁
  let F₂ := correspondenceIncidenceMap f g h₂ z w₂
  let : IsFinite F₁ := isFinite_correspondenceIncidenceMap f g h₁ z w₁ hz hw₁
  let : IsFinite F₂ := isFinite_correspondenceIncidenceMap f g h₂ z w₂ hz hw₂
  have he : F₁ ≫ j = (e).hom ≫ F₂ := by
    apply (cancel_epi (e₁).hom).mp
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc, F₁, F₂]
      using hj
  let c₁ := incidenceTorCycle f g h₁ z w₁ hw₁
  let c₂ := incidenceTorCycle f g h₂ z w₂ hw₂
  calc
    _ = finiteCyclePushforward j (finiteCyclePushforward F₁ c₁) :=
      congrArg (finiteCyclePushforward j) (incidenceTorCorrespondence_val f g h₁ z w₁ hz hw₁)
    _ = finiteCyclePushforward (F₁ ≫ j) c₁ := finiteCyclePushforward_comp_apply F₁ j c₁
    _ = finiteCyclePushforward ((e).hom ≫ F₂) c₁ :=
      DFunLike.congr_fun (finiteCyclePushforward_congr _ _ he) c₁
    _ = finiteCyclePushforward F₂ (finiteCyclePushforward (e).hom c₁) :=
      (finiteCyclePushforward_comp_apply (e).hom F₂ c₁).symm
    _ = finiteCyclePushforward F₂ c₂ :=
      congrArg (finiteCyclePushforward F₂)
        (reparametrizedIncidenceTorCycle_map U X Z₁ Z₂ z w₁ w₂
          p r l₁ l₂ hl₁ hl₂ eQ eP₁ eP₂ hQ hP₁ hP₂ hw₁ hw₂)
    _ = _ := (incidenceTorCorrespondence_val f g h₂ z w₂ hz hw₂).symm

end Stacks.Chow
