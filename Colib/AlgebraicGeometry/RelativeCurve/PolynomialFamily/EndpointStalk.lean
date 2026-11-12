/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PrincipalSection
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.ParameterGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.ParameterFiber
public import Colib.RingTheory.Ideal.PrincipalCut

/-! # Double cuts in the actual polynomial family stalk -/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.PolynomialSectionPencil

open AffineLineFiber Stacks.Chow

variable {k : Type u} [Field k] {D : Scheme.{u}}
  (t : D ⟶ Spec (.of k)) (a : k) (x : D) (s : Γ(parameterSpace t, ⊤))

local notation "y" => endpoint t a x
set_option quotPrecheck false in
local notation "R" => ((parameterSpace t).presheaf.stalk (endpoint t a x))
local notation "c" => scalar (parameterProjection t) a (endpoint t a x)
set_option quotPrecheck false in
local notation "g" => ((parameterSpace t).presheaf.germ ⊤ (endpoint t a x) (Opens.mem_top _) s)
set_option quotPrecheck false in
local notation "sₐ" => (D.presheaf.germ ⊤ x (Opens.mem_top _) ((endpoint t a).appTop s))

/-- The polynomial endpoint followed by the section cuts out its actual germ quotient. -/
theorem length_quotient_endpoint_section :
    Module.length R (R ⧸ (Ideal.span {c} ⊔ Ideal.span {g})) =
      Module.length (D.presheaf.stalk x) (D.presheaf.stalk x ⧸ Ideal.span {sₐ}) := by
  let f := ((endpoint t a).stalkMap x).hom
  have hf : Function.Surjective f := SurjectiveOnStalks.stalkMap_surjective _ _
  have hfg : f g = sₐ := (endpoint t a).germ_stalkMap_apply ⊤ x (Opens.mem_top _) s
  let e := Ideal.Quotient.mk (Ideal.span {f g})
  have he : Function.Surjective e := Ideal.Quotient.mk_surjective
  have h₁ := Module.length_self_eq_length_quotient_ker (e.comp f) (he.comp hf)
  have h₂ := Module.length_self_eq_length_quotient_ker e he
  have hk := Ideal.ker_quotient_mk_comp_of_surjective f hf g
  change RingHom.ker (e.comp f) = RingHom.ker f ⊔ Ideal.span {g} at hk
  rw [hk] at h₁
  change Module.length _ _ =
    Module.length R (R ⧸ (RingHom.ker ((endpoint t a).stalkMap x).hom ⊔
      Ideal.span {g})) at h₁
  rw [endpoint_stalkMap_ker t a x] at h₁
  change Module.length _ _ = Module.length (D.presheaf.stalk x)
    (D.presheaf.stalk x ⧸ RingHom.ker (Ideal.Quotient.mk (Ideal.span {f g}))) at h₂
  rw [Ideal.mk_ker] at h₂
  exact (h₁.symm.trans h₂).trans (congrArg (fun r : D.presheaf.stalk x =>
    Module.length (D.presheaf.stalk x) (D.presheaf.stalk x ⧸ Ideal.span {r})) hfg)

variable [IsIntegral D] [IsIntegral (parameterSpace t)]

/-- When the endpoint equation is nonzero, the parameter remains regular after
cutting by the original section. -/
theorem section_quotient_parameter_regular (hs : (endpoint t a).appTop s ≠ 0) :
    IsSMulRegular (R ⧸ Ideal.span {g}) c := by
  let e := endpointStalkQuotientEquiv t a x
  have hgs : e (Ideal.Quotient.mk _ g) = sₐ :=
    (endpointStalkQuotientEquiv_mk t a x _).trans
      ((endpoint t a).germ_stalkMap_apply ⊤ x (Opens.mem_top _) s)
  have hgn : sₐ ≠ 0 :=
    (map_ne_zero_iff _ (germ_injective_of_isIntegral D x (Opens.mem_top _))).mpr hs
  have hreg : IsSMulRegular (R ⧸ Ideal.span {c}) g := by
    intro u v huv
    apply e.injective
    apply mul_left_cancel₀ hgn
    change Ideal.Quotient.mk _ g * u = Ideal.Quotient.mk _ g * v at huv
    simpa only [map_mul, hgs] using congrArg e huv
  have hc : c ≠ 0 := by
    intro hz
    apply zero_ne_one (α := R)
    apply scalar_regular (parameterProjection t) a y
    change c • (0 : R) = c • (1 : R)
    simp only [hz, zero_smul]
  exact Ideal.isSMulRegular_quotient_span_singleton_swap c g hc hreg

local notation "m" => sectionToAffineLine (projection t ≫ t) s
local notation "i" => inclusion (sectionToAffineLine (projection t ≫ t) s) 0

/-- The actual zero scheme has regular parameter at every point over this endpoint. -/
theorem section_zero_parameter_regular (hs : (endpoint t a).appTop s ≠ 0)
    (z : fiber m 0) (hz : i z = y) :
    IsSMulRegular ((fiber m 0).presheaf.stalk z)
      (scalar (i ≫ parameterProjection t) a z) := by
  have hreg : IsSMulRegular
      ((parameterSpace t).presheaf.stalk (i z) ⧸ Ideal.span {scalar m 0 (i z)})
      (scalar (parameterProjection t) a (i z)) := by
    rw [sectionToAffineLine_zero_scalar, hz]
    exact section_quotient_parameter_regular t a x s hs
  let e := stalkQuotientEquiv m 0 z
  intro u v huv
  apply e.symm.injective
  apply hreg
  apply e.injective
  change e (Ideal.Quotient.mk _ (scalar (parameterProjection t) a (i z)) * e.symm u) =
    e (Ideal.Quotient.mk _ (scalar (parameterProjection t) a (i z)) * e.symm v)
  simp only [map_mul, e.apply_symm_apply, e, stalkQuotientEquiv_mk, ← scalar_comp]
  exact huv

end AlgebraicGeometry.Scheme.PolynomialSectionPencil
