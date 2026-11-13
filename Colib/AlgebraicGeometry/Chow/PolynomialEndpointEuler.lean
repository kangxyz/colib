/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Chow.WholePolynomialEndpointPushforward
public import Colib.RingTheory.Multiplicity.PrincipalEuler.Associativity
import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes

/-!
# Euler coefficients of polynomial endpoints

The endpoint of the fundamental cycle of a closed subscheme is computed
componentwise, with the generic lengths of the original subscheme. At a
proper intersection with finite stalk colength, that component sum is the
principal Euler integer of the original quotient stalk. This formula keeps
the scalar kernel when the endpoint equation is a zero divisor on that
quotient.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace AlgebraicGeometry.AlgebraicCycle

open _root_.AlgebraicGeometry.Scheme Scheme.AffineLineFiber Stacks.Chow

variable {k : Type u} [Field k] {D : Scheme.{u}} [IsNoetherian D]
  (f : D ⟶ Spec (.of (Polynomial k))) (a : k)

private theorem polynomialComponentEndpoint_eq_zero_of_not_specializes (x : fiber f a)
    (z : D) (h : ¬ z ⤳ inclusion f a x) :
    polynomialComponentEndpoint f a z x = 0 := by
  let J := integralComponentAt z
  let j := J.subschemeι
  let : IsNoetherian (fiber (j ≫ f) a) := isNoetherian_of_finiteType (inclusion (j ≫ f) a ≫ j)
  change finiteCyclePushforward (fiberMap f a j) (fundamentalCycle (fiber (j ≫ f) a)) x = 0
  apply finiteCyclePushforward_fundamentalCycle_eq_zero_of_notMem_range
  rintro ⟨w, hw⟩
  have hw' : j (inclusion (j ≫ f) a w) = inclusion f a x := by
    rw [← hw]
    exact (congrArg (fun m : fiber (j ≫ f) a ⟶ D => m w) (fiberMap_inclusion f a j)).symm
  have hr : inclusion f a x ∈ Set.range j := ⟨_, hw'⟩
  change inclusion f a x ∈ Set.range J.subschemeι at hr
  rw [J.range_subschemeι, coe_support_integralComponentAt] at hr
  exact h (specializes_iff_mem_closure.mpr hr)

private theorem polynomialComponentEndpoint_eq_quotientLength (x : fiber f a) (z : D)
    (h : Module.length (D.presheaf.stalk (inclusion f a x))
      (D.presheaf.stalk (inclusion f a x) ⧸
        (Ideal.span {scalar f a (inclusion f a x)} ⊔
          IdealSheafData.stalk (integralComponentAt z) (inclusion f a x))) ≠ ⊤) :
    polynomialComponentEndpoint f a z x =
      ((Module.length (D.presheaf.stalk (inclusion f a x))
        (D.presheaf.stalk (inclusion f a x) ⧸
          (Ideal.span {scalar f a (inclusion f a x)} ⊔
            IdealSheafData.stalk (integralComponentAt z) (inclusion f a x)))).toNat : ℤ) := by
  let J := integralComponentAt z
  let j := J.subschemeι
  let : IsNoetherian J.subscheme := isNoetherian_of_finiteType j
  have hI : closedImmersionQuotientStalkLength (fiberMap f a j ≫ inclusion f a)
      (inclusion f a x) = Module.length (D.presheaf.stalk (inclusion f a x))
        (D.presheaf.stalk (inclusion f a x) ⧸
          (Ideal.span {scalar f a (inclusion f a x)} ⊔
            IdealSheafData.stalk J (inclusion f a x))) := by
    rw [closedImmersionQuotientStalkLength, fiberMap_composite_stalk]
    exact congrArg (fun K : D.IdealSheafData => Module.length (D.presheaf.stalk (inclusion f a x))
      (D.presheaf.stalk (inclusion f a x) ⧸
        (Ideal.span {scalar f a (inclusion f a x)} ⊔ IdealSheafData.stalk K (inclusion f a x))))
      (Scheme.IdealSheafData.ker_subschemeι J)
  have hc := fiberMap_fundamentalCycle_apply_of_length_ne_top f a j x (hI.trans_ne h)
  exact hc.trans (congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) hI)

omit [IsNoetherian D] in
private theorem componentGenericPointsThrough_subschemeι_iff (Z : D.IdealSheafData)
    (y : D) (z : Z.subscheme) :
    Z.subschemeι z ∈ componentGenericPointsThrough Z y ↔
      z ∈ genericPoints Z.subscheme ∧ Z.subschemeι z ⤳ y := by
  have hm (w : Z.subscheme) : Z.subschemeι w ∈ (Z.support : Set D) := by
    rw [← Z.range_subschemeι]
    exact ⟨w, rfl⟩
  have he := Z.subschemeι.isClosedEmbedding
  constructor
  · rintro ⟨_, hs, hmax⟩
    refine ⟨mem_genericPoints_of_forall_specializes_eq (fun w hw => ?_), hs⟩
    exact he.injective (hmax _ (hm w) (he.isEmbedding.isInducing.specializes_iff.mpr hw))
  · rintro ⟨hz, hs⟩
    refine ⟨hm z, hs, fun w hw h => ?_⟩
    rw [← Z.range_subschemeι] at hw
    obtain ⟨w, rfl⟩ := hw
    exact congrArg Z.subschemeι
      (forall_specializes_eq_of_mem_genericPoints hz w
        (he.isEmbedding.isInducing.specializes_iff.mp h))

private theorem polynomialEndpointMap_pushforward_fundamentalCycle_apply_eq_finsum
    (Z : D.IdealSheafData) (x : fiber f a) :
    letI : IsNoetherian Z.subscheme := isNoetherian_of_finiteType Z.subschemeι
    let c := finiteCyclePushforward Z.subschemeι (fundamentalCycle Z.subscheme)
    polynomialEndpointMap f a c x =
      ∑ᶠ z ∈ componentGenericPointsThrough Z (inclusion f a x),
        c z * polynomialComponentEndpoint f a z x := by
  classical
  let : IsNoetherian Z.subscheme := isNoetherian_of_finiteType Z.subschemeι
  let : Fintype (genericPoints Z.subscheme) :=
    (fundamentalCycle_genericPoints_finite Z.subscheme).fintype
  let y := inclusion f a x
  let j := Z.subschemeι
  let c := finiteCyclePushforward j (fundamentalCycle Z.subscheme)
  let w (z : D) := c z * polynomialComponentEndpoint f a z x
  let T : Set (genericPoints Z.subscheme) := {z | j z.val ⤳ y}
  have hT : T.Finite := Set.toFinite _
  have hbij : Set.BijOn (fun z : genericPoints Z.subscheme => j z.val)
      T (componentGenericPointsThrough Z y) := by
    refine ⟨fun z hz => (componentGenericPointsThrough_subschemeι_iff Z y z.val).mpr
      ⟨z.property, hz⟩, fun z _ z' _ h => Subtype.ext (j.isClosedEmbedding.injective h), ?_⟩
    intro z hz
    obtain ⟨z', rfl⟩ : z ∈ Set.range j := by
      rw [Z.range_subschemeι]
      exact hz.1
    obtain ⟨hgen, hspec⟩ := (componentGenericPointsThrough_subschemeι_iff Z y z').mp hz
    exact ⟨⟨z', hgen⟩, hspec, rfl⟩
  change polynomialEndpointMap f a c x = ∑ᶠ z ∈ componentGenericPointsThrough Z y, w z
  calc
    _ = ∑ z : genericPoints Z.subscheme, w (j z.val) := by
      change polynomialEndpointMap f a
        (finiteCyclePushforward j (fundamentalCycle Z.subscheme)) x = _
      rw [fundamentalCycle, ofGenericCoefficients_eq_sum]
      simp only [map_sum, finiteCyclePushforward_single_of_isClosedImmersion,
        polynomialEndpointMap_single, coe_sum, Finset.sum_apply, coe_zsmul, Pi.smul_apply]
      apply Finset.sum_congr rfl
      intro z _
      unfold w c
      rw [finiteCyclePushforward_apply_of_isClosedImmersion, fundamentalCycle_apply_generic,
        zsmul_eq_mul]
      simp only [Int.cast_id]
    _ = ∑ᶠ z ∈ T, w (j z.val) := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hT]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro z _ hz
      have hn : ¬ j z.val ⤳ y := fun h => hz (hT.mem_toFinset.mpr h)
      unfold w
      rw [polynomialComponentEndpoint_eq_zero_of_not_specializes f a x (j z.val) hn, mul_zero]
    _ = _ := finsum_mem_eq_of_bijOn _ hbij fun _ _ => rfl

/-- The literal weighted endpoint coefficient of a closed subscheme equals the
principal Euler integer on its actual quotient stalk. Properness is required
on the reduced components through the point. The unreduced quotient stalk may
have scalar torsion. -/
theorem polynomialEndpointMap_pushforward_fundamentalCycle_apply_eq_principalEuler
    (Z : D.IdealSheafData) (x : fiber f a)
    (hfin : Module.length (D.presheaf.stalk (inclusion f a x))
      (D.presheaf.stalk (inclusion f a x) ⧸
        (Ideal.span {scalar f a (inclusion f a x)} ⊔
          IdealSheafData.stalk Z (inclusion f a x))) ≠ ⊤)
    (hproper : ∀ q : PrimeSpectrum (D.presheaf.stalk (inclusion f a x)),
      q.asIdeal ∈ (IdealSheafData.stalk Z (inclusion f a x)).minimalPrimes →
        scalar f a (inclusion f a x) ∉ q.asIdeal) :
    letI : IsNoetherian Z.subscheme := isNoetherian_of_finiteType Z.subschemeι
    polynomialEndpointMap f a (finiteCyclePushforward Z.subschemeι
        (fundamentalCycle Z.subscheme)) x =
      Module.principalEuler
        (N := D.presheaf.stalk (inclusion f a x) ⧸ IdealSheafData.stalk Z (inclusion f a x))
        (scalar f a (inclusion f a x)) := by
  classical
  let : IsNoetherian Z.subscheme := isNoetherian_of_finiteType Z.subschemeι
  let y := inclusion f a x
  let R := D.presheaf.stalk y
  let t := scalar f a y
  let I := IdealSheafData.stalk Z y
  let c := finiteCyclePushforward Z.subschemeι (fundamentalCycle Z.subscheme)
  have hlen : Module.length R
      ((R ⧸ I) ⧸ LinearMap.range (LinearMap.lsmul R (R ⧸ I) t)) ≠ ⊤ := by
    rw [AlgebraicGeometry.range_lsmul_eq_smul_top,
      (AlgebraicGeometry.quotSMulTopQuotientEquiv t I).length_eq]
    exact hfin
  have hmin : {q : PrimeSpectrum R | Minimal (· ∈ Module.support R (R ⧸ I)) q} =
      {q : PrimeSpectrum R | q.asIdeal ∈ I.minimalPrimes} := by
    ext q
    change Minimal (· ∈ Module.support R (R ⧸ I)) q ↔ q.asIdeal ∈ I.minimalPrimes
    rw [AlgebraicGeometry.minimal_support_iff, Ideal.annihilator_quotient]
  change polynomialEndpointMap f a c x = Module.principalEuler (N := R ⧸ I) t
  rw [polynomialEndpointMap_pushforward_fundamentalCycle_apply_eq_finsum,
    Module.principalEuler_associativity t (scalar_mem_maximalIdeal f a x) hlen, hmin]
  symm
  refine finsum_mem_eq_of_bijOn (D.fromSpecStalk y) (bijOn_fromSpecStalk_minimalPrimes Z y)
    fun q hq => ?_
  have hqgen := (fromSpecStalk_mem_componentGenericPointsThrough_iff Z y q).mpr hq
  obtain ⟨z, hz⟩ : D.fromSpecStalk y q ∈ Set.range Z.subschemeι := by
    rw [Z.range_subschemeι]
    exact hqgen.1
  have hzgen := ((componentGenericPointsThrough_subschemeι_iff Z y z).mp (hz ▸ hqgen)).1
  have hw : ((Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl (R ⧸ I))).toNat : ℤ) = c (D.fromSpecStalk y q) := by
    rw [length_localizedModule_quotient_idealStalk_eq_componentMultiplicity Z q ⟨z, hzgen⟩ hz.symm,
      componentMultiplicity_eq_length_stalk, ← hz]
    change _ = finiteCyclePushforward Z.subschemeι (fundamentalCycle Z.subscheme) (Z.subschemeι z)
    rw [finiteCyclePushforward_apply_of_isClosedImmersion,
      fundamentalCycle_apply_generic _ ⟨z, hzgen⟩]
  have hJ : IdealSheafData.stalk (integralComponentAt (D.fromSpecStalk y q)) y = q.asIdeal :=
    idealStalk_vanishingIdeal_closure_fromSpecStalk y q
  have hle : Ideal.span {t} ⊔ I ≤ Ideal.span {t} ⊔ q.asIdeal := sup_le_sup_left hq.1.2 _
  have hqfin : Module.length R (R ⧸ (Ideal.span {t} ⊔ q.asIdeal)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (Module.length_le_of_surjective
      (Submodule.factor hle) (Submodule.factor_surjective hle))
  rw [hw, Module.principalEuler_primeQuotient_eq_ord t q (hproper q hq),
    AlgebraicGeometry.ord_quotient_eq_length,
    polynomialComponentEndpoint_eq_quotientLength f a x (D.fromSpecStalk y q) (by
      change Module.length R (R ⧸ (Ideal.span {t} ⊔
        IdealSheafData.stalk (integralComponentAt (D.fromSpecStalk y q)) y)) ≠ ⊤
      rw [hJ]
      exact hqfin)]
  change c (D.fromSpecStalk y q) * _ =
    c (D.fromSpecStalk y q) * ((Module.length R (R ⧸ (Ideal.span {t} ⊔
      IdealSheafData.stalk (integralComponentAt (D.fromSpecStalk y q)) y))).toNat : ℤ)
  rw [hJ]

end AlgebraicGeometry.AlgebraicCycle
