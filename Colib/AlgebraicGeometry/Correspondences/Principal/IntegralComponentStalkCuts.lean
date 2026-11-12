/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.GraphEndpointTorCuts
public import Colib.AlgebraicGeometry.Correspondences.Principal.OrderWeights

/-!
# Local prime cuts on the original integral support

A prime of an actual scheme stalk determines its original integral closed
support and a genuine point above the original stalk point. The transported
closed-immersion stalk map has precisely that prime as kernel, so its full
principal quotient length is the full cut length on that original support.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable (X : Scheme.{u}) (x : X) (q : PrimeSpectrum (X.presheaf.stalk x))

/-- A local prime produces an actual point on its original integral closed support
above the original ambient point. -/
theorem exists_integralComponentAt_point_over_stalk :
    ∃ e : (integralComponentAt (X.fromSpecStalk x q)).subscheme,
      (integralComponentAt (X.fromSpecStalk x q)).subschemeι e = x := by
  rw [← Set.mem_range, (integralComponentAt (X.fromSpecStalk x q)).range_subschemeι,
    coe_support_integralComponentAt]
  exact (X.fromSpecStalk_specializes x q).mem_closure

/-- The actual point on the original support selected by the local prime. -/
def integralComponentPointOverStalk :
    (integralComponentAt (X.fromSpecStalk x q)).subscheme :=
  (exists_integralComponentAt_point_over_stalk X x q).choose

/-- This is a point above the unchanged original ambient point. -/
@[simp] theorem integralComponentPointOverStalk_inclusion :
    (integralComponentAt (X.fromSpecStalk x q)).subschemeι
      (integralComponentPointOverStalk X x q) = x :=
  (exists_integralComponentAt_point_over_stalk X x q).choose_spec

/-- The actual transported support stalk map has exactly the original local prime
as kernel, before any reduction of the endpoint quotient. -/
theorem integralComponentAt_transported_stalkMap_ker
    (e : (integralComponentAt (X.fromSpecStalk x q)).subscheme)
    (he : (integralComponentAt (X.fromSpecStalk x q)).subschemeι e = x) :
    RingHom.ker (((X.presheaf.stalkCongr (.of_eq he.symm)).hom ≫
      (integralComponentAt (X.fromSpecStalk x q)).subschemeι.stalkMap e).hom) = q.asIdeal := by
  rw [Scheme.Hom.transported_stalkMap_ker _ x e he.symm,
    Scheme.IdealSheafData.ker_subschemeι]
  exact idealStalk_vanishingIdeal_closure_fromSpecStalk x q

/-- Every actual local-prime principal cut is the full quotient on its original
integral support. The original global section is pulled back by that inclusion. -/
theorem integralComponentAt_primeCut_length
    (e : (integralComponentAt (X.fromSpecStalk x q)).subscheme)
    (he : (integralComponentAt (X.fromSpecStalk x q)).subschemeι e = x) (s : Γ(X, ⊤)) :
    Module.length (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ (q.asIdeal ⊔ Ideal.span {X.presheaf.germ ⊤ x (by trivial) s})) =
      Module.length ((integralComponentAt (X.fromSpecStalk x q)).subscheme.presheaf.stalk e)
        ((integralComponentAt (X.fromSpecStalk x q)).subscheme.presheaf.stalk e ⧸
          Ideal.span {((integralComponentAt (X.fromSpecStalk x q)).subscheme.presheaf.germ
            ⊤ e (by trivial)
            ((integralComponentAt (X.fromSpecStalk x q)).subschemeι.appTop s))}) := by
  let i := (integralComponentAt (X.fromSpecStalk x q)).subschemeι
  let φ := ((X.presheaf.stalkCongr (.of_eq he.symm)).hom ≫ i.stalkMap e).hom
  have H := Module.quotient_length_ker_sup_span φ
    (i.transported_stalkMap_surjective x e he.symm) (X.presheaf.germ ⊤ x (by trivial) s)
  rw [integralComponentAt_transported_stalkMap_ker X x q e he,
    Scheme.Hom.transported_stalkMap_globalSection i x e he.symm s] at H
  exact H

/-- Native local Euler associativity expressed on the actual original integral
supports, with full endpoint quotients at the actual points over the ambient point. -/
theorem principalCut_associativity_integralComponentStalks [IsLocallyNoetherian X]
    (n : X.presheaf.stalk x) (s : Γ(X, ⊤))
    (hsm : X.presheaf.germ ⊤ x (by trivial) s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hs : IsSMulRegular (X.presheaf.stalk x ⧸ Ideal.span {n})
      (X.presheaf.germ ⊤ x (by trivial) s))
    (hfinite : Module.length (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ (Ideal.span {X.presheaf.germ ⊤ x (by trivial) s} ⊔
        Ideal.span {n})) ≠ ⊤) :
    ((Module.length (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ (Ideal.span {X.presheaf.germ ⊤ x (by trivial) s} ⊔
        Ideal.span {n}))).toNat : ℤ) =
    ∑ᶠ q ∈ {q : PrimeSpectrum (X.presheaf.stalk x) |
        Minimal (· ∈ Module.support (X.presheaf.stalk x)
          (X.presheaf.stalk x ⧸ Ideal.span {n})) q},
      ((Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl (X.presheaf.stalk x ⧸ Ideal.span {n}))).toNat : ℤ) *
      let D := (integralComponentAt (X.fromSpecStalk x q)).subscheme
      let e := integralComponentPointOverStalk X x q
      ((Module.length (D.presheaf.stalk e)
        (D.presheaf.stalk e ⧸ Ideal.span {(D.presheaf.germ ⊤ e (by trivial)
          ((integralComponentAt (X.fromSpecStalk x q)).subschemeι.appTop s))})).toNat : ℤ) := by
  have hf : Module.length (X.presheaf.stalk x)
      ((X.presheaf.stalk x ⧸ Ideal.span {n}) ⧸
        LinearMap.range (LinearMap.lsmul (X.presheaf.stalk x)
          (X.presheaf.stalk x ⧸ Ideal.span {n}) (X.presheaf.germ ⊤ x (by trivial) s))) ≠ ⊤ := by
    rwa [Module.length_scalarCokernel_quotient]
  have H := Module.principalCokernel_associativity (X.presheaf.germ ⊤ x (by trivial) s)
    hsm hs hf
  rw [Module.length_scalarCokernel_quotient] at H
  rw [H]
  apply finsum_mem_congr rfl
  intro q _
  rw [Module.length_scalarCokernel_quotient, sup_comm,
    integralComponentAt_primeCut_length X x q (integralComponentPointOverStalk X x q)
      (integralComponentPointOverStalk_inclusion X x q) s]

end Stacks.Chow
