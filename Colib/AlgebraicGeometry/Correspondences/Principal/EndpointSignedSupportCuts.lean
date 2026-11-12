/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.SignedLocalPrincipalCuts

/-!
# Original polynomial endpoints supply the signed local support-cut identity

The actual endpoint stalk map and literal parameter equation supply regularity,
maximal-ideal membership and finite full quotient lengths. Neither endpoint
regularity nor component flatness is a caller-supplied comparison certificate.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open AlgebraicGeometry.PrincipalFamilyUnitOpen

attribute [local instance] Classical.propDecidable

universe u

namespace AlgebraicGeometry.PrincipalFamilyEndpointCuts

variable {k : Type u} [Field k] {W : Scheme.{u}} (p : W ⟶ Spec (.of k))
    [IsIntegral W] [IsNoetherian W]
    [IsIntegral (parameterSpace p)] [IsNoetherian (parameterSpace p)]

/-- The actual finite local-prime sum on the original polynomial cylinder.
It uses original orders and full cuts on the unchanged integral supports. -/
def signedEndpointSupportCoefficient (c : k) (x : W)
    (N D : Γ(parameterSpace p, ⊤)) : ℤ :=
  let P := parameterSpace p
  let y := endpoint p c x
  let n := P.presheaf.germ ⊤ y (by trivial) N
  let d := P.presheaf.germ ⊤ y (by trivial) D
  let hN := AlgebraicGeometry.finite_minimal_support
    (R := P.presheaf.stalk y) (M := P.presheaf.stalk y ⧸ Ideal.span {n})
  let hD := AlgebraicGeometry.finite_minimal_support
    (R := P.presheaf.stalk y) (M := P.presheaf.stalk y ⧸ Ideal.span {d})
  ∑ q ∈ hN.toFinset ∪ hD.toFinset,
    P.ord (algebraMap (P.presheaf.stalk y) P.functionField n /
      algebraMap (P.presheaf.stalk y) P.functionField d) (P.fromSpecStalk y q) *
        integralSupportCutLength P y (endpointEquation p c) q

/-- Actual endpoint germs supply all local associativity hypotheses and give the
full numerator-minus-denominator cut difference on the original cylinder. -/
theorem signedEndpointSupportCoefficient_eq_cutLengthDifference
    (c : k) (x : W) (hx : Order.coheight x = 1) (N D : Γ(parameterSpace p, ⊤))
    (hN : W.presheaf.germ ⊤ x (by trivial) ((endpoint p c).appTop N) ≠ 0)
    (hD : W.presheaf.germ ⊤ x (by trivial) ((endpoint p c).appTop D) ≠ 0) :
    signedEndpointSupportCoefficient p c x N D =
      ((cutLength p c x N).toNat : ℤ) - ((cutLength p c x D).toNat : ℤ) := by
  let P := parameterSpace p
  let y := endpoint p c x
  let R := P.presheaf.stalk y
  let n := P.presheaf.germ ⊤ y (by trivial) N
  let d := P.presheaf.germ ⊤ y (by trivial) D
  let t := P.presheaf.germ ⊤ y (by trivial) (endpointEquation p c)
  let φ := ((endpoint p c).stalkMap x).hom
  have hker : RingHom.ker φ = Ideal.span {t} := endpoint_stalkMap_ker_eq_parameter p c x
  have ht : IsSMulRegular R t :=
    PolynomialEndpointFiber.equation_germ_isSMulRegular_of_flat
      (pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) c y
  have htm : t ∈ IsLocalRing.maximalIdeal R := by
    apply IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ)
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton t)
  have hφn : φ n ≠ 0 := by simpa only [φ, n, y, P, endpoint_germ] using hN
  have hφd : φ d ≠ 0 := by simpa only [φ, d, y, P, endpoint_germ] using hD
  have hn : n ≠ 0 := fun hz => hφn (hz ▸ map_zero φ)
  have hd : d ≠ 0 := fun hz => hφd (hz ▸ map_zero φ)
  have hregular (a : R) (ha : φ a ≠ 0) : IsSMulRegular (R ⧸ Ideal.span {a}) t := by
    apply Module.isSMulRegular_quotient_span_swap t a ht
    rw [← hker]
    exact Module.isSMulRegular_quotient_ker_of_domain_image φ a ha
  have hfn : Module.length R (R ⧸ (Ideal.span {t} ⊔ Ideal.span {n})) ≠ ⊤ := by
    rw [← hker]
    exact endpoint_cut_finite p c x hx N hN
  have hfd : Module.length R (R ⧸ (Ideal.span {t} ⊔ Ideal.span {d})) ≠ ⊤ := by
    rw [← hker]
    exact endpoint_cut_finite p c x hx D hD
  have H := signed_ord_integralSupportCuts_eq_endpointDifference P y n d hn hd
    (endpointEquation p c) htm (hregular n hφn) (hregular d hφd) hfn hfd
  change signedEndpointSupportCoefficient p c x N D = _ at H
  rw [← hker] at H
  exact H

/-- The original signed support-cut sum is the already constructed actual weighted
endpoint Tor difference, with both full local principal weights retained. -/
theorem signedEndpointSupportCoefficient_eq_weightedTorDifference
    (c : k) (x : W) (hx : Order.coheight x = 1) (N D : Γ(parameterSpace p, ⊤))
    (hN : W.presheaf.germ ⊤ x (by trivial) ((endpoint p c).appTop N) ≠ 0)
    (hD : W.presheaf.germ ⊤ x (by trivial) ((endpoint p c).appTop D) ≠ 0) :
    signedEndpointSupportCoefficient p c x N D =
      weightedEndpointStalkTor p c x N - weightedEndpointStalkTor p c x D := by
  rw [signedEndpointSupportCoefficient_eq_cutLengthDifference p c x hx N D hN hD,
    weightedEndpointStalkTor_eq_cutLength p c x hx N hN,
    weightedEndpointStalkTor_eq_cutLength p c x hx D hD]

end AlgebraicGeometry.PrincipalFamilyEndpointCuts
