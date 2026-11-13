/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.EndpointCuts
public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor

/-!
# Signed endpoint cut lengths recover the original order

The signed difference uses the full local quotients by the actual endpoint stalk
kernel and the literal polynomial numerator and denominator. At zero the two
lengths cancel; at one their difference is the native order of the original local
fraction. This is a local length computation, not yet a graph-incidence Tor identity.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Order
open AlgebraicGeometry.PrincipalFamilyUnitOpen

universe u

namespace AlgebraicGeometry.PrincipalFamilyEndpointCuts

variable {k : Type u} [Field k] {W : Scheme.{u}} (p : W ⟶ Spec (.of k))

/-- Full ambient quotient length, without reducing either ideal or quotient. -/
abbrev cutLength (c : k) (x : W) (s : Γ(parameterSpace p, ⊤)) :=
  Module.length ((parameterSpace p).presheaf.stalk (endpoint p c x))
    (((parameterSpace p).presheaf.stalk (endpoint p c x)) ⧸
      (RingHom.ker ((endpoint p c).stalkMap x).hom ⊔
        Ideal.span {((parameterSpace p).presheaf.germ ⊤ (endpoint p c x) (by trivial) s)}))

/-- The actual numerator-minus-denominator local intersection coefficient. -/
def signedCutCoefficient (a b : Γ(W, ⊤)) (c : k) (x : W) : ℤ :=
  ((cutLength p c x (numerator p a b)).toNat : ℤ) -
    ((cutLength p c x (denominator p b)).toNat : ℤ)

/-- At zero both full local cuts have the same length, before taking their difference. -/
theorem numerator_cutLength_zero (a b : Γ(W, ⊤)) (x : W) :
    cutLength p 0 x (numerator p a b) = cutLength p 0 x (denominator p b) := by
  simp only [cutLength, endpoint_cut_length]
  erw [numerator_zero, denominator_endpoint]

@[simp] theorem signedCutCoefficient_zero (a b : Γ(W, ⊤)) (x : W) :
    signedCutCoefficient p a b 0 x = 0 := by
  rw [signedCutCoefficient, numerator_cutLength_zero, sub_self]

/-- The one endpoint recovers the native order of the same fraction of original germs.
Both nonzero germ hypotheses and codimension one are explicit. -/
@[colib_tag "COL-1218",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksFrontier/AlgebraicGeometry/Chow/RationalEquivalence/\
      FlatPullbackPrincipalDivisor.lean:585-594"
    "ingredient" "Native order of a codimension-one local fraction as a signed colength difference"]
theorem signedCutCoefficient_one [IsIntegral W] [IsNoetherian W]
    (a b : Γ(W, ⊤)) (x : W) (hx : coheight x = 1)
    (ha : W.presheaf.germ ⊤ x (by trivial) a ≠ 0)
    (hb : W.presheaf.germ ⊤ x (by trivial) b ≠ 0) :
    signedCutCoefficient p a b 1 x =
      W.ord (algebraMap (W.presheaf.stalk x) W.functionField
          (W.presheaf.germ ⊤ x (by trivial) a) /
        algebraMap (W.presheaf.stalk x) W.functionField
          (W.presheaf.germ ⊤ x (by trivial) b)) x := by
  simp only [signedCutCoefficient, cutLength, endpoint_cut_length]
  erw [numerator_one, denominator_endpoint]
  exact (Stacks.Chow.ord_div_algebraMap_eq_length_sub hx ha hb).symm

end AlgebraicGeometry.PrincipalFamilyEndpointCuts
