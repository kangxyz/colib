/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.EndpointTorCuts

/-!
# Genuine affine fractions supply the literal polynomial endpoint cuts

A nonzero rational function on an integral affine chart has a fraction of
actual global sections. Their germs remain nonzero at every chart point.
Consequently the literal numerator `t*a+(1-t)*b` and denominator `b` meet the
actual zero and one endpoints with the nonzero specialized germs needed for
the full quotient Tor calculation. No polynomial fraction equality is assumed.

The comparison with the original ambient polynomial rational function under
an arbitrary open chart is a separate function-field transport step.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace
open AlgebraicGeometry.PrincipalFamilyUnitOpen
open AlgebraicGeometry.PrincipalFamilyEndpointCuts

universe u

namespace AlgebraicGeometry.PrincipalFamilyEndpointCuts

variable {W : Scheme.{u}} [IsIntegral W] [IsAffine W]

local instance : Nonempty (⊤ : W.Opens) := ⟨⟨genericPoint W, by trivial⟩⟩

omit [IsIntegral W] [IsAffine W] in
/-- Equality to one on a nonempty original boundary forces the original section
itself to be nonzero. No reduction of the boundary is required. -/
theorem section_ne_zero_of_boundary {B : Scheme.{u}} (b : B ⟶ W) [Nonempty B]
    (f : Γ(W, ⊤)) (hf : b.appTop f = 1) : f ≠ 0 := by
  intro hz
  obtain ⟨y⟩ := (inferInstance : Nonempty B)
  have H := congrArg (fun s => B.presheaf.germ ⊤ y (by trivial) s) hf
  simp only [hz, map_zero, map_one] at H
  exact zero_ne_one H

/-- A genuine global fraction on an affine integral chart, with nonzero germs
at every point. The actual rational function is retained unchanged. -/
theorem exists_affineFraction (F : W.functionField) (hF : F ≠ 0) :
    ∃ a b : Γ(W, ⊤), W.germToFunctionField ⊤ a / W.germToFunctionField ⊤ b = F ∧
      ∀ x : W, W.presheaf.germ ⊤ x (by trivial) a ≠ 0 ∧
        W.presheaf.germ ⊤ x (by trivial) b ≠ 0 := by
  have := functionField_isFractionRing_of_isAffineOpen W ⊤ (isAffineOpen_top W)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective Γ(W, ⊤) F
  have ha : a ≠ 0 := by
    intro ha
    apply hF
    rw [← hab, ha, map_zero, zero_div]
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  refine ⟨a, b, hab, fun x => ⟨?_, ?_⟩⟩
  · exact fun hzero => ha ((germ_injective_of_isIntegral W x (by trivial))
      (hzero.trans (map_zero (W.presheaf.germ ⊤ x (by trivial)).hom).symm))
  · exact fun hzero => hb' ((germ_injective_of_isIntegral W x (by trivial))
      (hzero.trans (map_zero (W.presheaf.germ ⊤ x (by trivial)).hom).symm))

variable {k : Type u} [Field k] (p : W ⟶ Spec (.of k))

/-- The original affine fraction supplies the actual endpoint-germ regularity
and computes both signed full Tor cuts, with the original rational function. -/
theorem exists_affineFraction_endpointTor [IsNoetherian W]
    [IsNoetherian (parameterSpace p)] (F : W.functionField) (hF : F ≠ 0) :
    ∃ a b : Γ(W, ⊤), W.germToFunctionField ⊤ a / W.germToFunctionField ⊤ b = F ∧
      ∀ (x : W) (_hx : coheight x = 1),
        W.presheaf.germ ⊤ x (by trivial) ((endpoint p 0).appTop (numerator p a b)) ≠ 0 ∧
        W.presheaf.germ ⊤ x (by trivial) ((endpoint p 1).appTop (numerator p a b)) ≠ 0 ∧
        (∀ c : k, W.presheaf.germ ⊤ x (by trivial)
          ((endpoint p c).appTop (denominator p b)) ≠ 0) ∧
        weightedEndpointStalkTor p 0 x (numerator p a b) -
          weightedEndpointStalkTor p 0 x (denominator p b) = 0 ∧
        weightedEndpointStalkTor p 1 x (numerator p a b) -
          weightedEndpointStalkTor p 1 x (denominator p b) = W.ord F x := by
  obtain ⟨a, b, hab, hg⟩ := exists_affineFraction F hF
  refine ⟨a, b, hab, fun x hx => ?_⟩
  obtain ⟨ha, hb⟩ := hg x
  refine ⟨?_, ?_, ?_, weightedEndpointStalkTor_difference_zero p a b x hx hb, ?_⟩
  · simpa only [numerator_zero] using hb
  · simpa only [numerator_one] using ha
  · intro c
    simpa only [denominator_endpoint] using hb
  · rw [weightedEndpointStalkTor_difference_one p a b x hx ha hb,
      W.algebraMap_germ_eq_germToFunctionField (U := ⊤) (x := x) (by trivial) a,
      W.algebraMap_germ_eq_germToFunctionField (U := ⊤) (x := x) (by trivial) b, hab]

end AlgebraicGeometry.PrincipalFamilyEndpointCuts
