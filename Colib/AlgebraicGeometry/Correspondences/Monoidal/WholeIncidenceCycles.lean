/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Monoidal.ComponentTorDevissage
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.CompositionExpansion
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.WholeIncidenceComparison
import Colib.AlgebraicGeometry.Chow.FiniteOpenRestriction

/-!
# The actual whole exterior incidence cycle

Assemble the integer local Tor coefficients on the full product-support
incidence. Its finite outer map is the product of the two original finite
incidence maps. Pushing the whole cycle gives the original composition of the
two exterior primes.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace Stacks.Chow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] [PerfectField k]
  (X Y Z U V W : SmoothSite (Spec (.of k)))
  (a : pullback (C := Scheme) X.hom Y.hom)
  (b : pullback (C := Scheme) Y.hom Z.hom)
  (c : pullback (C := Scheme) U.hom V.hom)
  (d : pullback (C := Scheme) V.hom W.hom)
  (ha : IsFiniteCorrespondencePoint X.hom Y.hom a)
  (hb : IsFiniteCorrespondencePoint Y.hom Z.hom b)
  (hc : IsFiniteCorrespondencePoint U.hom V.hom c)
  (hd : IsFiniteCorrespondencePoint V.hom W.hom d)

local notation "D₁" =>
  correspondenceExteriorSupport X Y U V (integralComponentAt a) (integralComponentAt c)
local notation "D₂" =>
  correspondenceExteriorSupport Y Z V W (integralComponentAt b) (integralComponentAt d)
local notation "H" => correspondenceExteriorWholeIncidence X Y Z U V W a b c d
local notation "i" => correspondenceExteriorWholeIncidenceInclusion X Y Z U V W a b c d
local notation "l" =>
  correspondenceExteriorTarget X Y U V (integralComponentAt a) (integralComponentAt c)
local notation "r" =>
  correspondenceExteriorSource Y Z V W (integralComponentAt b) (integralComponentAt d)
local notation "sq" => correspondenceExteriorWholeIncidence_isPullback X Y Z U V W a b c d
set_option quotPrecheck false in
local notation "f" => (SmoothSite.product X U).hom
set_option quotPrecheck false in
local notation "g" => (SmoothSite.product Y V).hom
set_option quotPrecheck false in
local notation "h" => (SmoothSite.product Z W).hom
local notation "δ" => correspondenceTripleInclusion f g h

include ha hb hc hd in
omit [PerfectField k] in
/-- The original whole product-support incidence is of finite type over the Noetherian source. -/
theorem isNoetherian_correspondenceExteriorWholeIncidence : IsNoetherian H := by
  let : IsNoetherian D₁ := correspondenceExteriorSupport_isNoetherian X Y U V a c ha hc
  let : IsFinite (pullback.fst l r) :=
    exteriorWholeIncidenceFst_finite X Y Z U V W a b c d hb hd
  exact Scheme.isNoetherian_of_finiteType_of_isNoetherian (pullback.fst l r)

omit [PerfectField k] in
/-- The literal outer projection from the whole incidence of two product supports. -/
abbrev exteriorWholeIncidenceOuterMap : H ⟶ pullback f h :=
  i ≫ correspondenceTripleOuterProjection f g h

local notation "o" => exteriorWholeIncidenceOuterMap X Y Z U V W a b c d

omit [PerfectField k] in
@[reassoc]
private theorem exteriorWholeIncidenceOuterMap_fst :
    o ≫ pullback.fst f h = pullback.fst l r ≫
      correspondenceExteriorSource X Y U V (integralComponentAt a) (integralComponentAt c) := by
  have hfst : i ≫ pullback.fst (pullback.snd f g) (pullback.fst g h) =
      pullback.fst l r ≫
        correspondenceExteriorInclusion X Y U V (integralComponentAt a) (integralComponentAt c) :=
    pullback.lift_fst _ _ _
  rw [exteriorWholeIncidenceOuterMap, Category.assoc, correspondenceTripleOuterProjection_fst,
    ← Category.assoc, hfst, Category.assoc, correspondenceExteriorInclusion_fst]

omit [PerfectField k] in
@[reassoc]
private theorem exteriorWholeIncidenceOuterMap_snd :
    o ≫ pullback.snd f h = pullback.snd l r ≫
      correspondenceExteriorTarget Y Z V W (integralComponentAt b) (integralComponentAt d) := by
  have hsnd : i ≫ pullback.snd (pullback.snd f g) (pullback.fst g h) =
      pullback.snd l r ≫
        correspondenceExteriorInclusion Y Z V W (integralComponentAt b) (integralComponentAt d) :=
    pullback.lift_snd _ _ _
  rw [exteriorWholeIncidenceOuterMap, Category.assoc, correspondenceTripleOuterProjection_snd]
  change i ≫ pullback.snd (pullback.snd f g) (pullback.fst g h) ≫ pullback.snd g h = _
  rw [← Category.assoc, hsnd, Category.assoc, correspondenceExteriorInclusion_snd]

include ha hb hc hd in
omit [PerfectField k] in
/-- The whole outer map is finite, since its source projection is the composite of the
two actual finite projections. -/
theorem isFinite_exteriorWholeIncidenceOuterMap : IsFinite o := by
  let : IsFinite (pullback.fst l r) :=
    exteriorWholeIncidenceFst_finite X Y Z U V W a b c d hb hd
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt a)) := ha.1
  let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt c)) := hc.1
  let : IsFinite (o ≫ pullback.fst f h) := by
    rw [exteriorWholeIncidenceOuterMap_fst]
    infer_instance
  exact IsFinite.of_comp o (pullback.fst f h)

/-- The original whole incidence cycle with its actual signed Tor coefficients. -/
def exteriorWholeIncidenceTorCycle : AlgebraicCycle H ℤ :=
  letI := isNoetherian_correspondenceExteriorWholeIncidence X Y Z U V W a b c d ha hb hc hd
  AlgebraicCycle.ofGenericCoefficients (AlgebraicCycle.fundamentalCycle_genericPoints_finite H)
    (fun z => structureTorCoefficient (cartesianIntersectionGenericStalkMap sq z)
      ((δ).stalkMap (i z.val)).hom)

section Components

variable
  (α : genericPoints (correspondenceExteriorSupport X Y U V
    (integralComponentAt a) (integralComponentAt c)))
  (β : genericPoints (correspondenceExteriorSupport Y Z V W
    (integralComponentAt b) (integralComponentAt d)))

local notation "x" => leftComponentPoint X Y U V a c α
local notation "y" => rightComponentPoint Y Z V W b d β
local notation "L" => correspondenceIncidence f g h x y
local notation "m" => exteriorComponentIncidenceMap X Y Z U V W a b c d ha hb hc hd α β
local notation "hα" => correspondenceExteriorComponentPoint_admissible X Y U V a c ha hc α
local notation "hβ" => correspondenceExteriorComponentPoint_admissible Y Z V W b d hb hd β

omit [PerfectField k] in
private theorem exteriorComponentIncidenceMap_outer :
    m ≫ o = correspondenceIncidenceMap f g h x y := by
  apply pullback.hom_ext <;>
    simp [exteriorWholeIncidenceOuterMap, exteriorComponentIncidenceMap_inclusion_assoc,
      correspondenceIncidenceLeft, correspondenceIncidenceRight]

omit [PerfectField k] in
private theorem componentIncidenceTorCycle_push_apply (z : genericPoints H) :
    finiteCyclePushforward m (incidenceTorCycle f g h x y hβ) z.val =
      exteriorComponentTorCoefficientAt X Y Z U V W a b c d ha hb hc hd z α β := by
  classical
  by_cases hz : z.val ∈ Set.range m
  · obtain ⟨t, ht⟩ := hz
    let t₀ : genericPoints L := ⟨t, mem_genericPoints_of_isFinite_image m t
      (ht.symm ▸ z.property)⟩
    have hL : finiteCyclePushforward m (incidenceTorCycle f g h x y hβ) z.val =
        correspondenceIncidenceTorCoefficient k f g h x y t₀ := by
      rw [← ht, finiteCyclePushforward_apply_of_isClosedImmersion]
      exact incidenceTorCycle_apply_generic f g h x y hβ t₀
    rw [hL, exteriorComponentTorCoefficientAt]
    let t₁ : {z' : genericPoints L // m z'.val = z.val} := ⟨t₀, ht⟩
    let weight (t : {t : genericPoints L // m t.val = z.val}) : ℤ :=
      correspondenceIncidenceTorCoefficient k f g h x y t.val
    refine (finsum_eq_single weight t₁ ?_).symm
    intro s hs
    exact (hs (Subtype.ext (Subtype.ext
      ((m).isClosedEmbedding.injective (s.property.trans ht.symm))))).elim
  · have hzero : finiteCyclePushforward m (incidenceTorCycle f g h x y hβ) z.val = 0 := by
      by_contra hne
      exact hz (Set.image_subset_range _ _ (finiteCyclePushforward_support_subset m _ hne))
    have : IsEmpty {z' : genericPoints L // m z'.val = z.val} :=
      ⟨fun t => hz ⟨t.val.val, t.property⟩⟩
    rw [hzero, exteriorComponentTorCoefficientAt]
    exact (finsum_of_isEmpty _).symm

end Components

omit [PerfectField k] in
/-- Over an arbitrary field, preserve both input generic multiplicities in the native
component-cycle decomposition of the whole incidence. -/
theorem exteriorWholeIncidenceTorCycle_eq_weighted_sum :
    letI := correspondenceExteriorSupport_isNoetherian X Y U V a c ha hc
    letI := correspondenceExteriorSupport_isNoetherian Y Z V W b d hb hd
    letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₁).fintype
    letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₂).fintype
    exteriorWholeIncidenceTorCycle X Y Z U V W a b c d ha hb hc hd =
      ∑ α : genericPoints D₁, ∑ β : genericPoints D₂,
        (((Module.length ((D₁).presheaf.stalk α.val) ((D₁).presheaf.stalk α.val)).toNat : ℤ) *
          ((Module.length ((D₂).presheaf.stalk β.val) ((D₂).presheaf.stalk β.val)).toNat : ℤ)) •
        finiteCyclePushforward
          (exteriorComponentIncidenceMap X Y Z U V W a b c d ha hb hc hd α β)
          (incidenceTorCycle f g h
            (leftComponentPoint X Y U V a c α) (rightComponentPoint Y Z V W b d β)
            (correspondenceExteriorComponentPoint_admissible Y Z V W b d hb hd β)) := by
  classical
  let := correspondenceExteriorSupport_isNoetherian X Y U V a c ha hc
  let := correspondenceExteriorSupport_isNoetherian Y Z V W b d hb hd
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₁).fintype
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₂).fintype
  apply Function.locallyFinsuppWithin.ext
  intro z
  simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
    Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, smul_eq_mul]
  by_cases hz : z ∈ genericPoints H
  · let z₀ : genericPoints H := ⟨z, hz⟩
    change AlgebraicCycle.ofGenericCoefficients _ _ z₀.val = _
    rw [AlgebraicCycle.ofGenericCoefficients_apply_generic,
      structureTorCoefficient_eq_sum_weighted_componentIncidences X Y Z U V W a b c d
        ha hb hc hd z₀]
    exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
      congrArg (fun n : ℤ => _ * n)
        (componentIncidenceTorCycle_push_apply X Y Z U V W a b c d ha hb hc hd α β z₀).symm
  · change AlgebraicCycle.ofGenericCoefficients _ _ z = _
    rw [AlgebraicCycle.ofGenericCoefficients_apply_of_notMem _ _ _ hz]
    symm
    refine Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun β _ => ?_
    have hzero : finiteCyclePushforward
        (exteriorComponentIncidenceMap X Y Z U V W a b c d ha hb hc hd α β)
        (incidenceTorCycle f g h
          (leftComponentPoint X Y U V a c α) (rightComponentPoint Y Z V W b d β)
          (correspondenceExteriorComponentPoint_admissible Y Z V W b d hb hd β)) z = 0 := by
      by_contra hn
      obtain ⟨ξ, hξ, rfl⟩ := finiteCyclePushforward_support_subset
        (exteriorComponentIncidenceMap X Y Z U V W a b c d ha hb hc hd α β) _ hn
      exact hz (exteriorComponentIncidenceMap_mem_genericPoints X Y Z U V W a b c d
        ha hb hc hd α β ⟨ξ, support_incidenceTorCycle_subset f g h
          (leftComponentPoint X Y U V a c α) (rightComponentPoint Y Z V W b d β)
          (correspondenceExteriorComponentPoint_admissible Y Z V W b d hb hd β) hξ⟩)
    rw [hzero, mul_zero]

/-- The actual cycle of the whole incidence is the sum of the pushed native component cycles. -/
theorem exteriorWholeIncidenceTorCycle_eq_sum :
    letI := correspondenceExteriorSupport_isNoetherian X Y U V a c ha hc
    letI := correspondenceExteriorSupport_isNoetherian Y Z V W b d hb hd
    letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₁).fintype
    letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₂).fintype
    exteriorWholeIncidenceTorCycle X Y Z U V W a b c d ha hb hc hd =
      ∑ α : genericPoints D₁, ∑ β : genericPoints D₂,
        finiteCyclePushforward
          (exteriorComponentIncidenceMap X Y Z U V W a b c d ha hb hc hd α β)
          (incidenceTorCycle f g h
            (leftComponentPoint X Y U V a c α) (rightComponentPoint Y Z V W b d β)
            (correspondenceExteriorComponentPoint_admissible Y Z V W b d hb hd β)) := by
  classical
  let := correspondenceExteriorSupport_isNoetherian X Y U V a c ha hc
  let := correspondenceExteriorSupport_isNoetherian Y Z V W b d hb hd
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₁).fintype
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₂).fintype
  apply Function.locallyFinsuppWithin.ext
  intro z
  simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  by_cases hz : z ∈ genericPoints H
  · let z₀ : genericPoints H := ⟨z, hz⟩
    change AlgebraicCycle.ofGenericCoefficients _ _ z₀.val = _
    rw [AlgebraicCycle.ofGenericCoefficients_apply_generic,
      structureTorCoefficient_eq_sum_componentIncidences X Y Z U V W a b c d ha hb hc hd z₀]
    exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
      (componentIncidenceTorCycle_push_apply X Y Z U V W a b c d ha hb hc hd α β z₀).symm
  · change AlgebraicCycle.ofGenericCoefficients _ _ z = _
    rw [AlgebraicCycle.ofGenericCoefficients_apply_of_notMem _ _ _ hz]
    symm
    refine Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun β _ => ?_
    by_contra hn
    obtain ⟨ξ, hξ, rfl⟩ := finiteCyclePushforward_support_subset
      (exteriorComponentIncidenceMap X Y Z U V W a b c d ha hb hc hd α β) _ hn
    exact hz (exteriorComponentIncidenceMap_mem_genericPoints X Y Z U V W a b c d
      ha hb hc hd α β ⟨ξ, support_incidenceTorCycle_subset f g h
        (leftComponentPoint X Y U V a c α) (rightComponentPoint Y Z V W b d β)
        (correspondenceExteriorComponentPoint_admissible Y Z V W b d hb hd β) hξ⟩)

omit [PerfectField k] in
/-- Actual composition of the two exterior primes is the finite outer pushforward of the
whole exterior incidence's genuine Tor cycle. -/
theorem incidenceTorPairing_exteriorPrimes_val :
    letI : IsFinite o := isFinite_exteriorWholeIncidenceOuterMap X Y Z U V W a b c d ha hb hc hd
    (incidenceTorPairing f g h
      (correspondenceExteriorPrime X Y U V a c ha hc)
      (correspondenceExteriorPrime Y Z V W b d hb hd)).val =
      finiteCyclePushforward o
        (exteriorWholeIncidenceTorCycle X Y Z U V W a b c d ha hb hc hd) := by
  classical
  let : IsFinite o := isFinite_exteriorWholeIncidenceOuterMap X Y Z U V W a b c d ha hb hc hd
  let := correspondenceExteriorSupport_isNoetherian X Y U V a c ha hc
  let := correspondenceExteriorSupport_isNoetherian Y Z V W b d hb hd
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₁).fintype
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₂).fintype
  rw [incidenceTorPairing_exteriorPrimes_eq_sum, exteriorWholeIncidenceTorCycle_eq_weighted_sum,
    map_sum]
  change (finiteCorrespondences f h).subtype
    (∑ α : genericPoints D₁, ∑ β : genericPoints D₂, _) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [map_zsmul]
  change (correspondenceExteriorComponentWeight X Y U V a c α *
    correspondenceExteriorComponentWeight Y Z V W b d β) • _ =
    (correspondenceExteriorComponentWeight X Y U V a c α *
      correspondenceExteriorComponentWeight Y Z V W b d β) • _
  congr 1
  let x₀ := leftComponentPoint X Y U V a c α
  let y₀ := rightComponentPoint Y Z V W b d β
  let hα := correspondenceExteriorComponentPoint_admissible X Y U V a c ha hc α
  let hβ := correspondenceExteriorComponentPoint_admissible Y Z V W b d hb hd β
  let : IsFinite (correspondenceIncidenceMap f g h x₀ y₀) :=
    isFinite_correspondenceIncidenceMap f g h x₀ y₀ hα hβ
  let m₀ := exteriorComponentIncidenceMap X Y Z U V W a b c d ha hb hc hd α β
  let cycle := incidenceTorCycle f g h x₀ y₀ hβ
  change (incidenceTorCorrespondence f g h x₀ y₀ hα hβ).val =
    finiteCyclePushforward o (finiteCyclePushforward m₀ cycle)
  rw [incidenceTorCorrespondence_val, finiteCyclePushforward_comp_apply]
  exact finiteCyclePushforward_congr _ _
    (exteriorComponentIncidenceMap_outer X Y Z U V W a b c d ha hb hc hd α β).symm _

section ProductPushforward

local notation "I" => correspondenceIncidence X.hom Y.hom Z.hom a b
local notation "J" => correspondenceIncidence U.hom V.hom W.hom c d
local notation "F" => correspondenceIntersectionAmbientToField k X.hom Y.hom Z.hom
local notation "G" => correspondenceIntersectionAmbientToField k U.hom V.hom W.hom
local notation "p" => correspondenceIncidenceAmbientInclusion X.hom Y.hom Z.hom a b
local notation "q" => correspondenceIncidenceAmbientInclusion U.hom V.hom W.hom c d
local notation "leftOuter" => correspondenceIncidenceMap X.hom Y.hom Z.hom a b
local notation "v" => correspondenceIncidenceMap U.hom V.hom W.hom c d
local notation "IncidenceProduct" => pullback (C := Scheme) (p ≫ F) (q ≫ G)
local notation "e" => correspondenceWholeIncidenceIso X Y Z U V W a b c d
local notation "f₀" => pullback.fst X.hom Z.hom ≫ X.hom
local notation "g₀" => pullback.fst U.hom W.hom ≫ U.hom
local notation "η₁" => correspondenceWholeIncidenceFirstGeneric X Y Z U V W a b c d
local notation "η₂" => correspondenceWholeIncidenceSecondGeneric X Y Z U V W a b c d

omit [PerfectField k] in
private theorem correspondenceIncidence_left_over :
    p ≫ F = leftOuter ≫ f₀ := by
  rw [correspondenceIncidenceAmbientInclusion_base, ← Category.assoc,
    correspondenceIncidenceMap_fst]

omit [PerfectField k] in
private theorem correspondenceIncidence_right_over :
    q ≫ G = v ≫ g₀ := by
  rw [correspondenceIncidenceAmbientInclusion_base, ← Category.assoc,
    correspondenceIncidenceMap_fst]

private def correspondenceIncidenceProductOuter : IncidenceProduct ⟶ pullback f₀ g₀ :=
  pullback.map _ _ _ _ leftOuter v (𝟙 _)
    (by rw [Category.comp_id, correspondenceIncidence_left_over])
    (by rw [Category.comp_id, correspondenceIncidence_right_over])

local notation "b₀" => correspondenceIncidenceProductOuter X Y Z U V W a b c d
local notation "e₀" => correspondenceExteriorShuffle X Z U W

omit [PerfectField k] in
private theorem correspondenceIncidenceProductOuter_eq :
    b₀ ≫ (e₀).hom = (e).hom ≫ o := by
  have hfst : (correspondenceIncidenceOverAmbientIso X Y Z U V W a b c d).hom ≫ pullback.fst
      (correspondenceIncidenceLeft X.hom Y.hom Z.hom a b ≫ X.hom)
      (correspondenceIncidenceLeft U.hom V.hom W.hom c d ≫ U.hom) =
      pullback.fst (p ≫ F) (q ≫ G) :=
    pullback.lift_fst _ _ _
  have hsnd : (correspondenceIncidenceOverAmbientIso X Y Z U V W a b c d).hom ≫ pullback.snd
      (correspondenceIncidenceLeft X.hom Y.hom Z.hom a b ≫ X.hom)
      (correspondenceIncidenceLeft U.hom V.hom W.hom c d ≫ U.hom) =
      pullback.snd (p ≫ F) (q ≫ G) :=
    pullback.lift_snd _ _ _
  have hX : (e₀).hom ≫ pullback.fst f h ≫ pullback.fst X.hom U.hom =
      pullback.fst f₀ g₀ ≫ pullback.fst X.hom Z.hom :=
    pullbackFourShuffleIso_hom_fst_fst X.hom Z.hom U.hom W.hom
  have hU : (e₀).hom ≫ pullback.fst f h ≫ pullback.snd X.hom U.hom =
      pullback.snd f₀ g₀ ≫ pullback.fst U.hom W.hom :=
    pullbackFourShuffleIso_hom_fst_snd X.hom Z.hom U.hom W.hom
  have hZ : (e₀).hom ≫ pullback.snd f h ≫ pullback.fst Z.hom W.hom =
      pullback.fst f₀ g₀ ≫ pullback.snd X.hom Z.hom :=
    pullbackFourShuffleIso_hom_snd_fst X.hom Z.hom U.hom W.hom
  have hW : (e₀).hom ≫ pullback.snd f h ≫ pullback.snd Z.hom W.hom =
      pullback.snd f₀ g₀ ≫ pullback.snd U.hom W.hom :=
    pullbackFourShuffleIso_hom_snd_snd X.hom Z.hom U.hom W.hom
  have hb₁ : b₀ ≫ pullback.fst f₀ g₀ = pullback.fst (p ≫ F) (q ≫ G) ≫ leftOuter :=
    pullback.lift_fst _ _ _
  have hb₂ : b₀ ≫ pullback.snd f₀ g₀ = pullback.snd (p ≫ F) (q ≫ G) ≫ v :=
    pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, hX, reassoc_of% hb₁, correspondenceIncidenceMap_fst,
        exteriorWholeIncidenceOuterMap_fst_assoc, correspondenceExteriorSource_fst,
        correspondenceWholeIncidenceIso, Iso.trans_hom,
        correspondenceIncidenceProductIso_hom_first_assoc, reassoc_of% hfst]
      rfl
    · simp only [Category.assoc, hU, reassoc_of% hb₂, correspondenceIncidenceMap_fst,
        exteriorWholeIncidenceOuterMap_fst_assoc, correspondenceExteriorSource_snd,
        correspondenceWholeIncidenceIso, Iso.trans_hom,
        correspondenceIncidenceProductIso_hom_third_assoc, reassoc_of% hsnd]
      rfl
  · apply pullback.hom_ext
    · simp only [Category.assoc, hZ, reassoc_of% hb₁, correspondenceIncidenceMap_snd,
        exteriorWholeIncidenceOuterMap_snd_assoc, correspondenceExteriorTarget_fst,
        correspondenceWholeIncidenceIso, Iso.trans_hom,
        correspondenceIncidenceProductIso_hom_second_assoc, reassoc_of% hfst]
      rfl
    · simp only [Category.assoc, hW, reassoc_of% hb₂, correspondenceIncidenceMap_snd,
        exteriorWholeIncidenceOuterMap_snd_assoc, correspondenceExteriorTarget_snd,
        correspondenceWholeIncidenceIso, Iso.trans_hom,
        correspondenceIncidenceProductIso_hom_fourth_assoc, reassoc_of% hsnd]
      rfl

include ha hb hc hd in
omit [PerfectField k] in
private theorem isFinite_correspondenceIncidenceProductOuter : IsFinite b₀ := by
  let : IsFinite leftOuter := isFinite_correspondenceIncidenceMap X.hom Y.hom Z.hom a b ha hb
  let : IsFinite v := isFinite_correspondenceIncidenceMap U.hom V.hom W.hom c d hc hd
  exact MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance
    (correspondenceIncidence_left_over X Y Z a b) (correspondenceIncidence_right_over U V W c d)

omit [PerfectField k] in
private theorem isNoetherian_correspondenceIncidenceOverAmbient : IsNoetherian IncidenceProduct :=
   Scheme.isNoetherian_of_finiteType_of_isNoetherian (Y := Spec (.of k))
    (pullback.fst (p ≫ F) (q ≫ G) ≫ p ≫ F)

include ha hb hc hd in
private theorem exteriorWholeIncidenceTorCycle_eq_push_product :
    letI : DecidableEq H := Classical.decEq H
    letI : IsNoetherian IncidenceProduct :=
      isNoetherian_correspondenceIncidenceOverAmbient X Y Z U V W a b c d
    letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite IncidenceProduct).fintype
    exteriorWholeIncidenceTorCycle X Y Z U V W a b c d ha hb hc hd =
      ∑ t : genericPoints IncidenceProduct,
        single ((e).hom t.val)
          (correspondenceIncidenceTorCoefficient k X.hom Y.hom Z.hom a b (η₁ t) *
            correspondenceIncidenceTorCoefficient k U.hom V.hom W.hom c d (η₂ t)) := by
  classical
  let : IsNoetherian IncidenceProduct :=
    isNoetherian_correspondenceIncidenceOverAmbient X Y Z U V W a b c d
  let : IsNoetherian H := isNoetherian_correspondenceExteriorWholeIncidence
    X Y Z U V W a b c d ha hb hc hd
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite IncidenceProduct).fintype
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite H).fintype
  let φ : genericPoints IncidenceProduct ≃ genericPoints H :=
    { toFun := correspondenceWholeIncidenceGeneric X Y Z U V W a b c d
      invFun := fun z => ⟨(e).inv z.val, mem_genericPoints_of_flat (e).inv z.property⟩
      left_inv := fun t => Subtype.ext (by
        change (e).inv ((e).hom t.val) = t.val
        rw [← Scheme.Hom.comp_apply, (e).hom_inv_id]
        rfl)
      right_inv := fun t => Subtype.ext (by
        change (e).hom ((e).inv t.val) = t.val
        rw [← Scheme.Hom.comp_apply, (e).inv_hom_id]
        rfl) }
  simp only [exteriorWholeIncidenceTorCycle, AlgebraicCycle.ofGenericCoefficients_eq_sum]
  refine Fintype.sum_equiv φ.symm _ _ fun t => ?_
  have h₀ := structureTorCoefficient_wholeIncidence X Y Z U V W a b c d
    ha hb hc hd (φ.symm t)
  change structureTorCoefficient (cartesianIntersectionGenericStalkMap sq (φ (φ.symm t)))
    ((δ).stalkMap (i (φ (φ.symm t)).val)).hom = _ at h₀
  rw [φ.apply_symm_apply] at h₀
  change single t.val _ = single (φ (φ.symm t)).val _
  rw [φ.apply_symm_apply, h₀]

local notation "aI" => p ≫ F
local notation "aJ" => q ≫ G
local notation "c₁" => correspondenceIncidenceTorCoefficient k X.hom Y.hom Z.hom a b
local notation "c₂" => correspondenceIncidenceTorCoefficient k U.hom V.hom W.hom c d

private theorem exteriorPointCycle_apply_genericProduct
    (ξ : genericPoints I) (ζ : genericPoints J) (t : IncidenceProduct) :
    letI := Classical.propDecidable
    exteriorPointCycle aI aJ ξ.val ζ.val t =
      if pullback.fst aI aJ t = ξ.val then
        if pullback.snd aI aJ t = ζ.val then
          if t ∈ genericPoints IncidenceProduct then 1 else 0
        else 0
      else 0 := by
  classical
  let K := integralComponentAt ξ.val
  let K' := integralComponentAt ζ.val
  let A := pullback (K.subschemeι ≫ aI) (K'.subschemeι ≫ aJ)
  let j₀ := Scheme.Hom.productClosedMap aI aJ K.subschemeι K'.subschemeι
  let : IsIntegral K.subscheme := isIntegral_integralComponentAt ξ.val
  let : IsIntegral K'.subscheme := isIntegral_integralComponentAt ζ.val
  let : IsReduced A := isReduced_pullback_over_perfectField
    (K.subschemeι ≫ aI) (K'.subschemeι ≫ aJ)
  let : IsNoetherian A :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian
      (pullback.fst (K.subschemeι ≫ aI) (K'.subschemeι ≫ aJ) ≫ K.subschemeι ≫ aI)
  have hj : Set.range j₀ =
      (pullback.fst aI aJ) ⁻¹' closure ({ξ.val} : Set I) ∩
        (pullback.snd aI aJ) ⁻¹' closure ({ζ.val} : Set J) := by
    unfold j₀ Scheme.Hom.productClosedMap
    rw [Scheme.Pullback.range_map, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt,
      coe_support_integralComponentAt]
  have hp (s : genericPoints A) : pullback.fst aI aJ (j₀ s.val) = ξ.val ∧
      pullback.snd aI aJ (j₀ s.val) = ζ.val := by
    have hξ := mem_genericPoints_of_flat (pullback.fst (K.subschemeι ≫ aI)
      (K'.subschemeι ≫ aJ)) s.property
    have hζ := mem_genericPoints_of_flat (pullback.snd (K.subschemeι ≫ aI)
      (K'.subschemeι ≫ aJ)) s.property
    have hξ' : pullback.fst (K.subschemeι ≫ aI) (K'.subschemeι ≫ aJ) s.val =
        genericPoint K.subscheme := by
      simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hξ
    have hζ' : pullback.snd (K.subschemeι ≫ aI) (K'.subschemeι ≫ aJ) s.val =
        genericPoint K'.subscheme := by
      simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hζ
    constructor
    · have he : j₀ ≫ pullback.fst aI aJ =
          pullback.fst (K.subschemeι ≫ aI) (K'.subschemeι ≫ aJ) ≫ K.subschemeι :=
        pullback.lift_fst _ _ _
      exact (congrArg (fun f' : A ⟶ I => f' s.val) he).trans
        ((congrArg K.subschemeι hξ').trans (genericPointOf_integralComponentAt ξ.val))
    · have he : j₀ ≫ pullback.snd aI aJ =
          pullback.snd (K.subschemeι ≫ aI) (K'.subschemeι ≫ aJ) ≫ K'.subschemeι :=
        pullback.lift_snd _ _ _
      exact (congrArg (fun f' : A ⟶ J => f' s.val) he).trans
        ((congrArg K'.subschemeι hζ').trans (genericPointOf_integralComponentAt ζ.val))
  have hg (s : genericPoints A) : j₀ s.val ∈ genericPoints IncidenceProduct := by
    obtain ⟨h₁, h₂⟩ := hp s
    apply mem_genericPoints_of_forall_specializes_eq
    intro t ht
    have h₁' := forall_specializes_eq_of_mem_genericPoints ξ.property _
      (h₁ ▸ ht.map (pullback.fst aI aJ).continuous)
    have h₂' := forall_specializes_eq_of_mem_genericPoints ζ.property _
      (h₂ ▸ ht.map (pullback.snd aI aJ).continuous)
    obtain ⟨t', rfl⟩ : t ∈ Set.range j₀ := by
      rw [hj]
      exact ⟨h₁' ▸ subset_closure (Set.mem_singleton _), h₂' ▸ subset_closure
        (Set.mem_singleton _)⟩
    exact congrArg j₀ (forall_specializes_eq_of_mem_genericPoints s.property t'
      (j₀.isClosedEmbedding.isInducing.specializes_iff.mp ht))
  change finiteCyclePushforward j₀ (AlgebraicCycle.fundamentalCycle A) t = _
  by_cases h₁ : pullback.fst aI aJ t = ξ.val
  · by_cases h₂ : pullback.snd aI aJ t = ζ.val
    · by_cases ht : t ∈ genericPoints IncidenceProduct
      · obtain ⟨s, rfl⟩ : t ∈ Set.range j₀ := by
          rw [hj]
          exact ⟨h₁ ▸ subset_closure (Set.mem_singleton _), h₂ ▸ subset_closure
            (Set.mem_singleton _)⟩
        rw [finiteCyclePushforward_apply_of_isClosedImmersion,
          AlgebraicCycle.fundamentalCycle_apply_generic_of_isReduced A
            ⟨s, mem_genericPoints_of_isFinite_image j₀ s ht⟩]
        simp only [h₁, h₂, ht, ite_true]
      · simp only [h₁, h₂, ht, ite_true, ite_false]
        by_contra hn
        obtain ⟨s, hs, rfl⟩ := finiteCyclePushforward_support_subset j₀ _ hn
        exact ht (hg ⟨s, AlgebraicCycle.support_fundamentalCycle_subset A hs⟩)
    · simp only [h₁, h₂, ite_true, ite_false]
      by_contra hn
      obtain ⟨s, hs, rfl⟩ := finiteCyclePushforward_support_subset j₀ _ hn
      exact h₂ (hp ⟨s, AlgebraicCycle.support_fundamentalCycle_subset A hs⟩).2
  · simp only [h₁, ite_false]
    by_contra hn
    obtain ⟨s, hs, rfl⟩ := finiteCyclePushforward_support_subset j₀ _ hn
    exact h₁ (hp ⟨s, AlgebraicCycle.support_fundamentalCycle_subset A hs⟩).1

include ha hb hc hd in
private theorem exteriorWholeIncidenceTorCycle_eq_sum_exteriorPointCycle :
    letI : IsNoetherian IncidenceProduct :=
      isNoetherian_correspondenceIncidenceOverAmbient X Y Z U V W a b c d
    letI := (finite_genericPoints_correspondenceIncidence_of_smooth
      X.hom Y.hom Z.hom a b hb).fintype
    letI := (finite_genericPoints_correspondenceIncidence_of_smooth
      U.hom V.hom W.hom c d hd).fintype
    exteriorWholeIncidenceTorCycle X Y Z U V W a b c d ha hb hc hd =
      finiteCyclePushforward (e).hom (∑ ξ : genericPoints I, ∑ ζ : genericPoints J,
        (c₁ ξ * c₂ ζ) • exteriorPointCycle aI aJ ξ.val ζ.val) := by
  classical
  let : IsNoetherian IncidenceProduct :=
    isNoetherian_correspondenceIncidenceOverAmbient X Y Z U V W a b c d
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite IncidenceProduct).fintype
  let := (finite_genericPoints_correspondenceIncidence_of_smooth X.hom Y.hom Z.hom a b hb).fintype
  let := (finite_genericPoints_correspondenceIncidence_of_smooth U.hom V.hom W.hom c d hd).fintype
  rw [exteriorWholeIncidenceTorCycle_eq_push_product]
  have hcycle :
      (∑ t : genericPoints IncidenceProduct, single t.val (c₁ (η₁ t) * c₂ (η₂ t))) =
      ∑ ξ : genericPoints I, ∑ ζ : genericPoints J,
        (c₁ ξ * c₂ ζ) • exteriorPointCycle aI aJ ξ.val ζ.val := by
    apply Function.locallyFinsuppWithin.ext
    intro t
    simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
      Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, smul_eq_mul]
    simp_rw [exteriorPointCycle_apply_genericProduct X Y Z U V W a b c d]
    by_cases ht : t ∈ genericPoints IncidenceProduct
    · let t₀ : genericPoints IncidenceProduct := ⟨t, ht⟩
      rw [Finset.sum_eq_single t₀]
      · rw [Finset.sum_eq_single (η₁ t₀)]
        · rw [Finset.sum_eq_single (η₂ t₀)]
          · simp [t₀, correspondenceWholeIncidenceFirstGeneric,
              correspondenceWholeIncidenceSecondGeneric, ht, single_apply]
          · intro ζ _ hne
            have hne' : pullback.snd aI aJ t ≠ ζ.val := fun he => hne (Subtype.ext he.symm)
            simp [hne']
          · simp
        · intro ξ _ hne
          have hne' : pullback.fst aI aJ t ≠ ξ.val := fun he => hne (Subtype.ext he.symm)
          simp [hne']
        · simp
      · intro w _ hne
        have hne' : t ≠ w.val := fun he => hne (Subtype.ext he.symm)
        simp [single_apply, hne']
      · simp
    · have hz : ∀ w : genericPoints IncidenceProduct, t ≠ w.val :=
        fun w he => ht (he.symm ▸ w.property)
      simp [single_apply, ht, hz]
  rw [← hcycle, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact (finiteCyclePushforward_single_of_isClosedImmersion (e).hom t.val _).symm

/-- Interchange on the four actual prime cycles uses the full signed Tor coefficients and the
full degrees of the two finite incidence maps. -/
theorem incidenceTorPairing_exteriorPrimes :
    incidenceTorPairing f g h
      (correspondenceExteriorPrime X Y U V a c ha hc)
      (correspondenceExteriorPrime Y Z V W b d hb hd) =
    correspondenceExterior X Z U W
      (incidenceTorCorrespondence X.hom Y.hom Z.hom a b ha hb)
      (incidenceTorCorrespondence U.hom V.hom W.hom c d hc hd) := by
  classical
  let : IsFinite o := isFinite_exteriorWholeIncidenceOuterMap X Y Z U V W a b c d ha hb hc hd
  let : IsFinite b₀ := isFinite_correspondenceIncidenceProductOuter
    X Y Z U V W a b c d ha hb hc hd
  let : IsFinite leftOuter := isFinite_correspondenceIncidenceMap X.hom Y.hom Z.hom a b ha hb
  let : IsFinite v := isFinite_correspondenceIncidenceMap U.hom V.hom W.hom c d hc hd
  let := (finite_genericPoints_correspondenceIncidence_of_smooth X.hom Y.hom Z.hom a b hb).fintype
  let := (finite_genericPoints_correspondenceIncidence_of_smooth U.hom V.hom W.hom c d hd).fintype
  apply Subtype.ext
  rw [incidenceTorPairing_exteriorPrimes_val,
    exteriorWholeIncidenceTorCycle_eq_sum_exteriorPointCycle, finiteCyclePushforward_comp_apply]
  have h₀ := correspondenceIncidenceProductOuter_eq X Y Z U V W a b c d
  rw [finiteCyclePushforward_congr _ _ h₀.symm, ← finiteCyclePushforward_comp_apply]
  rw [correspondenceExterior_incidencePrimes_eq_sum, map_sum, map_sum]
  change ∑ ξ : genericPoints I, finiteCyclePushforward (e₀).hom
    (finiteCyclePushforward b₀ (∑ ζ : genericPoints J,
      (c₁ ξ * c₂ ζ) • exteriorPointCycle aI aJ ξ.val ζ.val)) =
    (finiteCorrespondences f h).subtype (∑ ξ : genericPoints I, ∑ ζ : genericPoints J, _)
  rw [map_sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  have hf := correspondenceIncidence_left_over X Y Z a b
  have hg := correspondenceIncidence_right_over U V W c d
  have hpush : finiteCyclePushforward b₀ (exteriorPointCycle aI aJ ξ.val ζ.val) =
      (((leftOuter).residueDegree ξ.val : ℤ) * ((v).residueDegree ζ.val : ℤ)) •
        exteriorPointCycle f₀ g₀ (leftOuter ξ.val) (v ζ.val) :=
    finiteCyclePushforward_exteriorPointCycle aI aJ f₀ g₀ leftOuter v hf hg ξ.val ζ.val
  have hξ := isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic
    X.hom Y.hom Z.hom a b ha hb ξ
  have hζ := isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic
    U.hom V.hom W.hom c d hc hd ζ
  rw [map_zsmul, hpush, map_zsmul, map_zsmul,
    finiteCyclePushforward_shuffle_exteriorPointCycle X Z U W (leftOuter ξ.val) (v ζ.val)
      hξ hζ, smul_smul]
  let d₁ : ℤ := (leftOuter).residueDegree ξ.val
  let d₂ : ℤ := (v).residueDegree ζ.val
  rw [show (c₁ ξ * c₂ ζ) * (d₁ * d₂) = (c₁ ξ * d₁) * (c₂ ζ * d₂) by ac_rfl]
  rfl

end ProductPushforward

end Stacks.Chow
