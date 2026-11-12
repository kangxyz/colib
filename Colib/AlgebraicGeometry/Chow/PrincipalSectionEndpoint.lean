/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.WholePolynomialEndpointPushforward
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.EndpointStalk

/-! # Endpoint coefficients of a regular section cycle

At an original coheight-one point of the endpoint, the entire section
fiber has the finite length of the actual double cut.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Cycles/PrincipalDivisor/Faces/`
`PrincipalDivisorFaceCoefficient.lean` at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicCycle

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.AffineLineFiber
open _root_.AlgebraicGeometry.Scheme.PolynomialSectionPencil
open Stacks.Chow

variable {k : Type u} [Field k] {D : Scheme.{u}} [IsIntegral D] [IsNoetherian D]
  (t : D ⟶ Spec (.of k)) (a : k) (s : Γ(parameterSpace t, ⊤))

/-- The whole endpoint of the original section cycle reads as the order
of the actual specialized section. -/
theorem polynomialEndpointMap_sectionZero_apply
    (x : D) (hx : coheight x = 1) (hs : (endpoint t a).appTop s ≠ 0) :
    polynomialEndpointMap (parameterProjection t) a (sectionZeroCycle (projection t ≫ t) s)
        ((endpointFiberIso t a).hom x) =
      D.ord (sectionRationalFunction ((endpoint t a).appTop s)) x := by
  let f := parameterProjection t
  let g := sectionToAffineLine (projection t ≫ t) s
  let i := inclusion g 0
  let q := fiberMap f a i
  let z := (endpointFiberIso t a).hom x
  let r := D.presheaf.germ ⊤ x (Opens.mem_top x) ((endpoint t a).appTop s)
  let : Ring.KrullDimLE 1 (D.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hr : r ≠ 0 :=
    (map_ne_zero_iff _ (germ_injective_of_isIntegral D x (Opens.mem_top x))).mpr hs
  have hz : inclusion f a z = endpoint t a x :=
    congrArg (fun j : D ⟶ parameterSpace t => j x) (endpointFiberIso_hom_inclusion t a)
  have hlen : closedImmersionQuotientStalkLength (q ≫ inclusion f a) (inclusion f a z) =
      Module.length (D.presheaf.stalk x) (D.presheaf.stalk x ⧸ Ideal.span {r}) := by
    unfold closedImmersionQuotientStalkLength
    rw [show q = fiberMap f a i from rfl, fiberMap_composite_stalk, inclusion_stalk,
      show g = sectionToAffineLine (projection t ≫ t) s from rfl,
      sectionToAffineLine_zero_scalar, hz]
    exact length_quotient_endpoint_section t a x s
  have hfin : closedImmersionQuotientStalkLength (q ≫ inclusion f a) (inclusion f a z) ≠ ⊤ := by
    rw [hlen]
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_iff_ne_zero.mpr hr))
  have hpush : finiteCyclePushforward q (polynomialEndpointMap (i ≫ f) a
      (fundamentalCycle (fiber g 0))) z =
      finiteCyclePushforward q (fundamentalCycle (fiber (i ≫ f) a)) z := by
    by_cases h : z ∈ Set.range q
    · obtain ⟨y, hy⟩ := h
      have hfin' : Module.length ((fiber (i ≫ f) a).presheaf.stalk y)
          ((fiber (i ≫ f) a).presheaf.stalk y) ≠ ⊤ := by
        rw [← closedImmersionQuotientStalkLength_image (q ≫ inclusion f a) y]
        exact (congrArg (closedImmersionQuotientStalkLength (q ≫ inclusion f a))
          (congrArg (inclusion f a) hy)).symm ▸ hfin
      have hygen := mem_genericPoints_of_stalk_length_ne_top y hfin'
      have hi : i (inclusion (i ≫ f) a y) = endpoint t a x := by
        have he := congrArg (fun j : fiber (i ≫ f) a ⟶ parameterSpace t => j y)
          (fiberMap_inclusion f a i)
        exact he.symm.trans ((congrArg (inclusion f a) hy).trans hz)
      rw [← hy, finiteCyclePushforward_apply_of_isClosedImmersion,
        finiteCyclePushforward_apply_of_isClosedImmersion]
      exact polynomialEndpointMap_fundamentalCycle_apply_of_regular (i ≫ f) a ⟨y, hygen⟩
        (section_zero_parameter_regular t a x s hs _ hi)
    · have hzero (c : AlgebraicCycle (fiber (i ≫ f) a) ℤ) :
          finiteCyclePushforward q c z = 0 := by
        by_contra h'
        obtain ⟨y, _, hy⟩ := finiteCyclePushforward_support_subset q c h'
        exact h ⟨y, hy⟩
      exact (hzero _).trans (hzero _).symm
  rw [sectionZeroCycle, polynomialEndpointMap_pushforward_closed]
  change finiteCyclePushforward q (polynomialEndpointMap (i ≫ f) a
    (fundamentalCycle (fiber g 0))) z = _
  rw [hpush, fiberMap_fundamentalCycle_apply_of_length_ne_top f a i z hfin, hlen]
  let : Nonempty (⊤ : D.Opens) := ⟨⟨x, Opens.mem_top x⟩⟩
  exact (ord_germ_eq_quotient_length ⊤ _ hs (Opens.mem_top x) hx).symm

end AlgebraicGeometry.AlgebraicCycle
