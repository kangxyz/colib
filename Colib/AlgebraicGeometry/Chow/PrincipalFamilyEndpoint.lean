/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PolynomialEndpointRestriction
public import Colib.AlgebraicGeometry.Chow.PolynomialEndpointSupport
public import Colib.AlgebraicGeometry.Chow.PrincipalSectionEndpoint
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyFraction

/-! # Signed endpoint coefficients of the original rational family

The numerator and denominator retain the full scheme-theoretic fibers.
Adapted from `Motivic/Aglib/AlgebraicGeometry/Cycles/PrincipalDivisor/Faces/`
`PrincipalFamilyChartEndpointCoefficients.lean` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Order TopologicalSpace Stacks.Chow
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.AffineLineFiber
open _root_.AlgebraicGeometry.Scheme.PolynomialSectionPencil
open _root_.AlgebraicGeometry.AlgebraicCycle

local instance dominantIntegralOpen {D E : Scheme.{u}} [IsIntegral D] [IsIntegral E]
    (i : D ⟶ E) [IsOpenImmersion i] : IsDominant i :=
  ((tfae_isDominant_of_isIntegral i).out 1 2).mpr (genericPoint_eq_of_isOpenImmersion i)

variable {k : Type u} [Field k] {C W : Scheme.{u}}
  [IsIntegral C] [IsNoetherian C] [IsIntegral W] [IsLocallyNoetherian W]
  (p : C ⟶ Spec (.of k)) (v : W ⟶ C) [IsOpenImmersion v]
  (f : Γ(W, ⊤)) [Nonempty (unitOpen (v ≫ p) f)] [Nonempty (ambientUnitOpen p v f)]

/-- The native principal cycle of the same interpolating rational function. -/
def originalOrderCycle : AlgebraicCycle (parameterSpace p) ℤ :=
  principalCycle (parameterSpace p) (ambientRationalFunction p v f)

variable (U : C.Opens) [IsIntegral U.toScheme] [IsNoetherian U.toScheme]
  (b d : Γ(U.toScheme, ⊤)) (hd : d ≠ 0)
  (hfrac : sectionRationalFunction b / sectionRationalFunction d =
    dominantFunctionFieldMap U.ι (openSectionGerm v f))

local notation "q" => U.ι ≫ p

include hd hfrac in
/-- On a chosen chart the original endpoint coefficient is the signed order
of the two actual restricted sections. -/
theorem originalOrderCycle_endpoint_chart_apply (a : k)
    (hN : (endpoint q a).appTop (numerator q b d) ≠ 0)
    (x : U.toScheme) (hx : coheight x = 1) :
    polynomialEndpointMap (parameterProjection p) a (originalOrderCycle p v f)
        ((endpointFiberIso p a).hom (U.ι x)) =
      U.toScheme.ord (sectionRationalFunction ((endpoint q a).appTop (numerator q b d))) x -
        U.toScheme.ord (sectionRationalFunction d) x := by
  let j := parameterMap p U.ι
  let N := numerator q b d
  let D := denominator q d
  let p' := projection q ≫ q
  let c := sectionZeroCycle p' N - sectionZeroCycle p' D
  have hN0 : N ≠ 0 := fun h => hN (by rw [show numerator q b d = N from rfl, h, map_zero])
  have hD0 : D ≠ 0 := fun h => hd (by
    rw [← denominator_endpoint q a d, show denominator q d = D from rfl, h, map_zero])
  have hchart (z : parameterSpace q) : c z = originalOrderCycle p v f (j z) := by
    dsimp only [c]
    rw [sectionZeroCycle_sub_eq_principalCycle p' N D hN0 hD0, ←
      ambientRationalFunction_chart_fraction p v f U b d hd hfrac]
    simp only [originalOrderCycle, principalCycle_apply]
    exact ord_dominantFunctionFieldMap_of_isOpenImmersion j
      (ambientRationalFunction p v f) z
  have he : j ≫ parameterProjection p = parameterProjection q := parameterMap_snd p U.ι
  have h := polynomialEndpointMap_open_apply_of_comp_eq (parameterProjection p) a j
    (parameterProjection q) he (originalOrderCycle p v f) c hchart
    ((endpointFiberIso q a).hom x)
  change polynomialEndpointMap (parameterProjection q) a c ((endpointFiberIso q a).hom x) =
    polynomialEndpointMap (parameterProjection p) a (originalOrderCycle p v f)
      (parameterFiberMap p U.ι a ((endpointFiberIso q a).hom x)) at h
  have hface : parameterFiberMap p U.ι a ((endpointFiberIso q a).hom x) =
      (endpointFiberIso p a).hom (U.ι x) :=
    congrArg (fun g : U.toScheme ⟶ fiber (parameterProjection p) a => g x)
      (endpointFiberIso_hom_parameterFiberMap p U.ι a)
  rw [hface] at h
  refine h.symm.trans ?_
  simp only [c, map_sub, coe_sub, Pi.sub_apply]
  rw [polynomialEndpointMap_sectionZero_apply q a N x hx hN,
    polynomialEndpointMap_sectionZero_apply q a D x hx
      (by simpa only [D, denominator_endpoint] using hd)]
  simp only [N, D, denominator_endpoint]

omit [IsNoetherian C] [IsLocallyNoetherian W] in
/-- The specified open section is nonzero as a rational germ. -/
theorem openSectionGerm_ne_zero (hf : f ≠ 0) : openSectionGerm v f ≠ 0 := by
  let : Nonempty (v ''ᵁ (⊤ : W.Opens)) :=
    ⟨⟨v (genericPoint W), ⟨genericPoint W, Opens.mem_top _, rfl⟩⟩⟩
  unfold openSectionGerm
  apply (map_ne_zero_iff _ (C.germToFunctionField_injective _)).mpr
  exact (map_ne_zero_iff _ (ConcreteCategory.bijective_of_isIso (v.appIso ⊤).inv).1).mpr hf

omit [IsNoetherian C] in
/-- Presenting the original section on its open subscheme gives the same rational germ. -/
theorem openSectionGerm_topIso (U : C.Opens) [Nonempty U] [IsIntegral U.toScheme]
    (s : Γ(C, U)) : openSectionGerm U.ι (U.topIso.inv s) = C.germToFunctionField U s := by
  unfold openSectionGerm
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  exact C.presheaf.germ_res_apply (eqToHom U.ι_image_top) _ _ s

/-- The signed family has zero coefficient at the original zero face and
the original rational coefficient at the one face. -/
theorem originalOrderCycle_endpoints_apply (hf : f ≠ 0) (x : C) (hx : coheight x = 1) :
    polynomialEndpointMap (parameterProjection p) 0 (originalOrderCycle p v f)
        ((endpointFiberIso p 0).hom x) = 0 ∧
      polynomialEndpointMap (parameterProjection p) 1 (originalOrderCycle p v f)
        ((endpointFiberIso p 1).hom x) = C.ord (openSectionGerm v f) x := by
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let x' : V.toScheme := ⟨x, hxV⟩
  have hxV' : V.ι x' = x := rfl
  let : Nonempty V := ⟨x'⟩
  let : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  let : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (V : Set C)) }
  let : IsAffine V.toScheme := hV
  let : Nonempty (⊤ : V.toScheme.Opens) := ⟨⟨x', Opens.mem_top x'⟩⟩
  let : IsFractionRing Γ(V.toScheme, ⊤) V.toScheme.functionField :=
    functionField_isFractionRing_of_isAffineOpen V.toScheme ⊤ (isAffineOpen_top _)
  let r := dominantFunctionFieldMap V.ι (openSectionGerm v f)
  have hr : r ≠ 0 :=
    (map_ne_zero_iff _ (dominantFunctionFieldMap V.ι).injective).mpr
      (openSectionGerm_ne_zero v f hf)
  obtain ⟨b, d, hd, hfrac⟩ := IsFractionRing.div_surjective Γ(V.toScheme, ⊤) r
  change sectionRationalFunction b / sectionRationalFunction d = r at hfrac
  have hd0 : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hb0 : b ≠ 0 := by
    intro hb
    apply hr
    rw [← hfrac, hb, sectionRationalFunction, map_zero, zero_div]
  have hx' : coheight x' = 1 := by
    rw [← coheight_eq_of_isOpenImmersion V.ι]
    exact hx
  constructor
  · have h := originalOrderCycle_endpoint_chart_apply p v f V b d hd0 hfrac 0
      (by simpa only [numerator_zero] using hd0) x' hx'
    simpa only [hxV', numerator_zero, sub_self] using h
  · have h := originalOrderCycle_endpoint_chart_apply p v f V b d hd0 hfrac 1
      (by simpa only [numerator_one] using hb0) x' hx'
    rw [numerator_one, hxV'] at h
    have hd' : sectionRationalFunction d ≠ 0 :=
      (map_ne_zero_iff _ (V.toScheme.germToFunctionField_injective ⊤)).mpr hd0
    have hratio := V.toScheme.ord_mul (x := x')
      (f := sectionRationalFunction b / sectionRationalFunction d)
      (g := sectionRationalFunction d) (hfrac.symm ▸ hr) hd'
    rw [div_mul_cancel₀ _ hd'] at hratio
    have hdiff : V.toScheme.ord (sectionRationalFunction b) x' -
        V.toScheme.ord (sectionRationalFunction d) x' = V.toScheme.ord r x' := by
      rw [← hfrac]
      omega
    have hrestrict := ord_dominantFunctionFieldMap_of_isOpenImmersion V.ι
      (openSectionGerm v f) x'
    rw [hxV'] at hrestrict
    exact h.trans (hdiff.trans hrestrict)

/-- If the actual parameter is flat on each nonzero component, the signed
endpoint formulas hold at every point of the entire original scheme. -/
theorem originalOrderCycle_endpoints_apply_all [LocallyOfFiniteType p] (hf : f ≠ 0)
    (hflat : ∀ z, originalOrderCycle p v f z ≠ 0 →
      Flat ((integralComponentAt z).subschemeι ≫ parameterProjection p)) (x : C) :
    polynomialEndpointMap (parameterProjection p) 0 (originalOrderCycle p v f)
        ((endpointFiberIso p 0).hom x) = 0 ∧
      polynomialEndpointMap (parameterProjection p) 1 (originalOrderCycle p v f)
        ((endpointFiberIso p 1).hom x) = C.ord (openSectionGerm v f) x := by
  by_cases hx : coheight x = 1
  · exact originalOrderCycle_endpoints_apply p v f hf x hx
  have h (a : k) :
      polynomialEndpointMap (parameterProjection p) a (originalOrderCycle p v f)
        ((endpointFiberIso p a).hom x) = 0 := by
    rw [polynomialEndpointMap_apply_coeff]
    apply Finset.sum_eq_zero
    intro z hz
    have hc : originalOrderCycle p v f z ≠ 0 :=
      (Function.locallyFinsupp.finite_support (originalOrderCycle p v f)).mem_toFinset.mp hz
    have hcodim : coheight z = 1 := by
      by_contra h'
      exact hc (Scheme.ord_eq_zero_of_coheight_neq_one h' _)
    let : Flat ((integralComponentAt z).subschemeι ≫ parameterProjection p) := hflat z hc
    have hz0 : polynomialComponentEndpoint (parameterProjection p) a z
        ((endpointFiberIso p a).hom x) = 0 := by
      by_contra h'
      exact hx (polynomialComponentEndpoint_coheight_one p a z hcodim x h')
    rw [hz0, mul_zero]
  exact ⟨h 0, (h 1).trans (Scheme.ord_eq_zero_of_coheight_neq_one hx _).symm⟩

section Retained

variable {V : Scheme.{u}} [IsIntegral V] [IsNoetherian V] (j : V ⟶ C) [IsOpenImmersion j]

/-- The same original interpolating divisor on the retained product. -/
def retainedFamilyCycle : AlgebraicCycle (parameterSpace (j ≫ p)) ℤ :=
  principalCycle (parameterSpace (j ≫ p))
    (dominantFunctionFieldMap (parameterMap p j) (ambientRationalFunction p v f))

/-- The prescribed original rational function on the retained scheme. -/
def retainedOrderCycle : AlgebraicCycle V ℤ :=
  principalCycle V (dominantFunctionFieldMap j (openSectionGerm v f))

/-- Both entire retained endpoint cycles preserve every original coefficient. -/
theorem retainedFamilyCycle_endpoints [LocallyOfFiniteType p] (hf : f ≠ 0)
    (hflat : ∀ z, originalOrderCycle p v f z ≠ 0 →
      Flat ((integralComponentAt z).subschemeι ≫ parameterProjection p)) :
    polynomialEndpointMap (parameterProjection (j ≫ p)) 0 (retainedFamilyCycle p v f j) = 0 ∧
      polynomialEndpointMap (parameterProjection (j ≫ p)) 1 (retainedFamilyCycle p v f j) =
        finiteCyclePushforward (endpointFiberIso (j ≫ p) 1).hom (retainedOrderCycle v f j) := by
  have hcompare (a : k) (x : V) :
      polynomialEndpointMap (parameterProjection (j ≫ p)) a (retainedFamilyCycle p v f j)
          ((endpointFiberIso (j ≫ p) a).hom x) =
        polynomialEndpointMap (parameterProjection p) a (originalOrderCycle p v f)
          ((endpointFiberIso p a).hom (j x)) := by
    have hcoeff (z : parameterSpace (j ≫ p)) :
        retainedFamilyCycle p v f j z = originalOrderCycle p v f (parameterMap p j z) :=
      ord_dominantFunctionFieldMap_of_isOpenImmersion (parameterMap p j)
        (ambientRationalFunction p v f) z
    have h := polynomialEndpointMap_open_apply_of_comp_eq (parameterProjection p) a
      (parameterMap p j) (parameterProjection (j ≫ p)) (parameterMap_snd p j)
      (originalOrderCycle p v f) (retainedFamilyCycle p v f j) hcoeff
      ((endpointFiberIso (j ≫ p) a).hom x)
    change _ = polynomialEndpointMap (parameterProjection p) a (originalOrderCycle p v f)
      (parameterFiberMap p j a ((endpointFiberIso (j ≫ p) a).hom x)) at h
    have hface := congrArg (fun g : V ⟶ fiber (parameterProjection p) a => g x)
      (endpointFiberIso_hom_parameterFiberMap p j a)
    exact h.trans (congrArg (fun y : fiber (parameterProjection p) a =>
      polynomialEndpointMap (parameterProjection p) a (originalOrderCycle p v f) y) hface)
  constructor
  · apply Function.locallyFinsuppWithin.ext
    intro z
    obtain ⟨x, rfl⟩ := (endpointFiberIso (j ≫ p) 0).hom.surjective z
    rw [hcompare]
    exact (originalOrderCycle_endpoints_apply_all p v f hf hflat (j x)).1
  · apply Function.locallyFinsuppWithin.ext
    intro z
    obtain ⟨x, rfl⟩ := (endpointFiberIso (j ≫ p) 1).hom.surjective z
    rw [hcompare, finiteCyclePushforward_apply_of_isClosedImmersion]
    exact (originalOrderCycle_endpoints_apply_all p v f hf hflat (j x)).2.trans
      (ord_dominantFunctionFieldMap_of_isOpenImmersion j (openSectionGerm v f) x).symm

end Retained

end AlgebraicGeometry.PrincipalFamilyUnitOpen
