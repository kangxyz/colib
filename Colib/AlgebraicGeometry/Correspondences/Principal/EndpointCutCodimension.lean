/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.EndpointParameterCuts
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.StalkwiseRegular
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension

/-!
# Generic points of the full original endpoint cut

A dominant map from an integral scheme to the polynomial line has an effective
Cartier endpoint kernel. Native Cartier codimension therefore supplies coheight
one at every generic point of the whole scheme-theoretic endpoint fibre.
No flatness of that integral scheme over the parameter is assumed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Native Cartier codimension applies to the original closed immersion, using
its actual kernel-image isomorphism without reducing its domain. -/
theorem coheight_eq_one_of_effective_kernel {D P : Scheme.{u}}
    [IsLocallyNoetherian P] (j : D ⟶ P) [IsClosedImmersion j]
    (hj : Stacks.Divisors.IsEffectiveCartierDivisor j.ker) (x : genericPoints D) :
    Order.coheight (j x.val) = 1 := by
  let y : genericPoints j.ker.subscheme :=
    ⟨j.toImage x.val, mem_genericPoints_of_flat j.toImage x.property⟩
  have H := ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor j.ker hj y.val
    ⟨genericPoints.component y, genericPoints.isGenericPoint y⟩
  rw [ringKrullDim_stalk_eq_coheight] at H
  simp only [y, ← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι] at H
  exact_mod_cast H

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Chow.PolynomialEndpointFiber

variable {k : Type u} [Field k] {P : Scheme.{u}} [IsIntegral P]
    [IsLocallyNoetherian P] (f : P ⟶ Spec (.of (Polynomial k))) [IsDominant f] (c : k)

/-- The full native endpoint kernel is Cartier, using actual parameter dominance. -/
theorem fiberInclusion_ker_isEffectiveCartierDivisor :
    Stacks.Divisors.IsEffectiveCartierDivisor (fiberInclusion f c).ker := by
  refine isEffectiveCartierDivisor_of_stalk_regular_principal _ fun x _ => ?_
  refine ⟨P.presheaf.germ ⊤ x (by trivial) (equation f c), ?_,
    fiberInclusion_ker_stalk f c x⟩
  apply IsRegular.of_ne_zero
  exact fun hz => equation_ne_zero_of_isDominant f c
    ((germ_injective_of_isIntegral P x (by trivial)) (hz.trans (map_zero _).symm))

/-- Every generic point of the full literal endpoint fibre maps to coheight one
in the integral support, without support flatness. -/
theorem fiberInclusion_generic_coheight (x : genericPoints (fiber f c)) :
    Order.coheight (fiberInclusion f c x.val) = 1 :=
  (fiberInclusion f c).coheight_eq_one_of_effective_kernel
    (fiberInclusion_ker_isEffectiveCartierDivisor f c) x

end Stacks.Chow.PolynomialEndpointFiber
