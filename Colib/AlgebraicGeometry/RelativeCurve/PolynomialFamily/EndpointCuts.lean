/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyUnitOpen
public import Colib.RingTheory.Length.SurjectiveQuotient
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Local lengths of the actual principal polynomial endpoint cuts

The numerator is literally `t*a+(1-t)*b` and the denominator is the pullback of `b`.
The quotient uses the kernel of the actual endpoint stalk map and the equation germ.
Its full length is finite at a codimension-one point with nonzero specialized germ.
Neither flatness of a finite support nor an incidence Tor comparison is assumed.

Adapted from the 2026-10-21 Motivic checkpoint,
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/PolynomialFamily/PrincipalFamilyEndpointCuts.lean`.
The ring-length comparison now uses the native Stacks ring equivalence theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Order
open AlgebraicGeometry.PrincipalFamilyUnitOpen

universe u

namespace AlgebraicGeometry.PrincipalFamilyEndpointCuts

variable {k : Type u} [Field k] {W : Scheme.{u}} (p : W ⟶ Spec (.of k))

/-- The original polynomial numerator, without choosing a divisor replacement. -/
def numerator (a b : Γ(W, ⊤)) : Γ(parameterSpace p, ⊤) :=
  parameter p * (projection p).appTop a +
    (1 - parameter p) * (projection p).appTop b

/-- The unchanged polar denominator. -/
def denominator (b : Γ(W, ⊤)) : Γ(parameterSpace p, ⊤) :=
  (projection p).appTop b

private theorem endpoint_projection_section (c : k) (s : Γ(W, ⊤)) :
    (endpoint p c).appTop ((projection p).appTop s) = s := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, endpoint_projection]
  simp

@[simp] theorem numerator_zero (a b : Γ(W, ⊤)) :
    (endpoint p 0).appTop (numerator p a b) = b := by
  simp [numerator, endpoint_parameter, endpoint_projection_section]

@[simp] theorem numerator_one (a b : Γ(W, ⊤)) :
    (endpoint p 1).appTop (numerator p a b) = a := by
  simp [numerator, endpoint_parameter, endpoint_projection_section]

@[simp] theorem denominator_endpoint (b : Γ(W, ⊤)) (c : k) :
    (endpoint p c).appTop (denominator p b) = b :=
  endpoint_projection_section p c b

private theorem endpoint_closed (c : k) : IsClosedImmersion (endpoint p c) := by
  have : IsAffineHom (projection p) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance
  have : IsClosedImmersion (endpoint p c ≫ projection p) := by
    rw [endpoint_projection]
    infer_instance
  exact IsClosedImmersion.of_comp (endpoint p c) (projection p)

/-- Restriction is through the actual original endpoint stalk map. -/
theorem endpoint_germ (c : k) (x : W) (s : Γ(parameterSpace p, ⊤)) :
    (endpoint p c).stalkMap x
        ((parameterSpace p).presheaf.germ ⊤ (endpoint p c x) (by trivial) s) =
      W.presheaf.germ ⊤ x (by trivial) ((endpoint p c).appTop s) := by
  simp [Scheme.Hom.appTop]
  rfl

/-- The full ambient cut length equals the original specialized local quotient length. -/
theorem endpoint_cut_length (c : k) (x : W) (s : Γ(parameterSpace p, ⊤)) :
    Module.length ((parameterSpace p).presheaf.stalk (endpoint p c x))
      (((parameterSpace p).presheaf.stalk (endpoint p c x)) ⧸
        (RingHom.ker ((endpoint p c).stalkMap x).hom ⊔
          Ideal.span {((parameterSpace p).presheaf.germ ⊤ (endpoint p c x)
            (by trivial) s)})) =
      Module.length (W.presheaf.stalk x)
        ((W.presheaf.stalk x) ⧸ Ideal.span
          {W.presheaf.germ ⊤ x (by trivial) ((endpoint p c).appTop s)}) := by
  have := endpoint_closed p c
  rw [Module.quotient_length_ker_sup_span ((endpoint p c).stalkMap x).hom
    ((endpoint p c).stalkMap_surjective x)]
  rw [show ((endpoint p c).stalkMap x).hom
      ((parameterSpace p).presheaf.germ ⊤ (endpoint p c x) (by trivial) s) =
      W.presheaf.germ ⊤ x (by trivial) ((endpoint p c).appTop s) from
    endpoint_germ p c x s]

/-- A nonzero original face germ gives finite length of the full ambient cut.
The kernel is the actual endpoint map's kernel, not a supplied principal ideal. -/
theorem endpoint_cut_finite [IsIntegral W] [IsNoetherian W]
    (c : k) (x : W) (hx : coheight x = 1) (s : Γ(parameterSpace p, ⊤))
    (hs : W.presheaf.germ ⊤ x (by trivial) ((endpoint p c).appTop s) ≠ 0) :
    Module.length ((parameterSpace p).presheaf.stalk (endpoint p c x))
      (((parameterSpace p).presheaf.stalk (endpoint p c x)) ⧸
        (RingHom.ker ((endpoint p c).stalkMap x).hom ⊔
          Ideal.span {((parameterSpace p).presheaf.germ ⊤ (endpoint p c x)
            (by trivial) s)})) ≠ ⊤ := by
  have := endpoint_closed p c
  let φ := ((endpoint p c).stalkMap x).hom
  rw [Module.quotient_length_ker_sup_span φ ((endpoint p c).stalkMap_surjective x)]
  have : Ring.KrullDimLE 1 (W.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hnonzero : φ ((parameterSpace p).presheaf.germ ⊤ (endpoint p c x)
      (by trivial) s) ≠ 0 := by
    change (endpoint p c).stalkMap x
      ((parameterSpace p).presheaf.germ ⊤ (endpoint p c x) (by trivial) s) ≠ 0
    rwa [endpoint_germ]
  exact Module.length_ne_top_iff.mpr
    (isFiniteLength_quotient_span_singleton (W.presheaf.stalk x)
      (mem_nonZeroDivisors_iff_ne_zero.mpr hnonzero))

/-- Both literal signed-family terms have nonzero original images and finite
whole cuts at zero and one. No termwise reduction or cancellation is performed. -/
theorem numerator_denominator_cuts_finite [IsIntegral W] [IsNoetherian W]
    (a b : Γ(W, ⊤)) (x : W) (hx : coheight x = 1)
    (ha : W.presheaf.germ ⊤ x (by trivial) a ≠ 0)
    (hb : W.presheaf.germ ⊤ x (by trivial) b ≠ 0)
    (c : k) (hc : c = 0 ∨ c = 1)
    (s : Γ(parameterSpace p, ⊤)) (hs : s = numerator p a b ∨ s = denominator p b) :
    Module.length ((parameterSpace p).presheaf.stalk (endpoint p c x))
      (((parameterSpace p).presheaf.stalk (endpoint p c x)) ⧸
        (RingHom.ker ((endpoint p c).stalkMap x).hom ⊔
          Ideal.span {((parameterSpace p).presheaf.germ ⊤ (endpoint p c x)
            (by trivial) s)})) ≠ ⊤ := by
  apply endpoint_cut_finite p c x hx s
  rcases hs with rfl | rfl
  · rcases hc with rfl | rfl
    · simpa only [numerator_zero] using hb
    · simpa only [numerator_one] using ha
  · simpa only [denominator_endpoint] using hb

end AlgebraicGeometry.PrincipalFamilyEndpointCuts
