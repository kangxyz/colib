/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Intersection.AffineLineFiber
public import Colib.AlgebraicGeometry.Chow.FiniteFlatFundamental
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentSum
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.IntersectionInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import Mathlib.RingTheory.KrullDimension.Regular

/-!
# Whole endpoint multiplicities in the actual family stalk

At a generic point of the full fiber of a flat Noetherian scheme over A1, the
original family local ring is one-dimensional: its quotient by the literal
regular parameter is the zero-dimensional fiber local ring. Native Stacks
02QG expresses its colength as the sum over all minimal primes, with their
full local lengths. The native `fromSpecStalk` correspondence reindexes these
primes by the actual global generic components through the fiber point.

The resulting equality is a local coefficient theorem for the whole fiber.
It does not assert a graph-precomposition theorem, or silently assume that
every component fiber has generic image in the whole fiber. The latter needs
the finite-flat source geometry when passing from these generic coefficients
to an equality of ungraded global cycles.

The source construction is motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
RelativeCurve/Endpoints/FiniteFlatCurveSpecialization.lean. Here native Stacks
02QG and its actual-stalk prime correspondence replace the original separate
cycle/Koszul-Euler comparison. All quotient maps are the actual stalk maps
constructed in `Intersection.AffineLineFiber`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.AffineLineFiber

open Stacks.Chow

variable {k : Type u} [Field k] {D : Scheme.{u}}
  (f : D ⟶ Spec (.of (Polynomial k))) (a : k)

instance fiber_isNoetherian [IsNoetherian D] : IsNoetherian (fiber f a) :=
  { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (inclusion f a)
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (inclusion f a) }

/-- The true quotient length is finite at every generic point of the whole fiber. -/
theorem length_stalk_quotient_ne_top [IsNoetherian D]
    (x : genericPoints (fiber f a)) :
    Module.length (D.presheaf.stalk (inclusion f a x.val))
      (D.presheaf.stalk (inclusion f a x.val) ⧸
        Ideal.span {scalar f a (inclusion f a x.val)}) ≠ ⊤ := by
  rw [length_stalk_quotient]
  exact AlgebraicCycle.fundamentalCycle_length_ne_top (fiber f a) x

/-- The whole original local ring, not its reduction, has dimension one at a
component of the endpoint fiber. This follows from the actual regular cut. -/
theorem ringKrullDim_stalk_eq_one_of_regular [IsNoetherian D]
    (x : genericPoints (fiber f a))
    (hreg : IsSMulRegular (D.presheaf.stalk (inclusion f a x.val))
      (scalar f a (inclusion f a x.val))) :
    ringKrullDim (D.presheaf.stalk (inclusion f a x.val)) = 1 := by
  have hzero : ringKrullDim (D.presheaf.stalk (inclusion f a x.val) ⧸
      Ideal.span {scalar f a (inclusion f a x.val)}) = 0 :=
    (ringKrullDim_eq_of_ringEquiv (stalkQuotientEquiv f a x.val)).trans
      ((ringKrullDim_stalk_eq_zero_iff_mem_genericPoints (fiber f a) x.val).mpr x.property)
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
    hreg (scalar_mem_maximalIdeal f a x.val)
  simpa only [hzero, zero_add] using hdim.symm

/-- A flat polynomial family supplies the regular cut at each endpoint. -/
theorem ringKrullDim_stalk_eq_one [IsNoetherian D] [Flat f]
    (x : genericPoints (fiber f a)) :
    ringKrullDim (D.presheaf.stalk (inclusion f a x.val)) = 1 :=
  ringKrullDim_stalk_eq_one_of_regular f a x (scalar_regular f a _)

/-- Stacks 02QG on the actual whole family stalk. Every minimal local component
retains its original length, and every endpoint quotient remains unreduced. -/
theorem fundamentalCycle_apply_eq_finsum_minimalPrimes_of_regular [IsNoetherian D]
    (x : genericPoints (fiber f a))
    (hreg : IsSMulRegular (D.presheaf.stalk (inclusion f a x.val))
      (scalar f a (inclusion f a x.val))) :
    AlgebraicCycle.fundamentalCycle (fiber f a) x.val =
      ∑ᶠ p : {p : PrimeSpectrum (D.presheaf.stalk (inclusion f a x.val)) //
          p.asIdeal ∈ minimalPrimes (D.presheaf.stalk (inclusion f a x.val))},
        ((Module.length (Localization.AtPrime p.val.asIdeal)
            (Localization.AtPrime p.val.asIdeal)).toNat : ℤ) *
          ((Module.length (D.presheaf.stalk (inclusion f a x.val))
            (D.presheaf.stalk (inclusion f a x.val) ⧸
              (Ideal.span {scalar f a (inclusion f a x.val)} ⊔ p.val.asIdeal))).toNat : ℤ) := by
  rw [AlgebraicCycle.fundamentalCycle_apply_generic,
    ← length_stalk_quotient f a x.val]
  exact natCast_length_quotient_span_eq_sum_minimalPrimes
    (scalar f a (inclusion f a x.val)) hreg
    (ringKrullDim_stalk_eq_one_of_regular f a x hreg) (length_stalk_quotient_ne_top f a x)

/-- A flat polynomial family supplies the regular cut at each endpoint. -/
theorem fundamentalCycle_apply_eq_finsum_minimalPrimes [IsNoetherian D] [Flat f]
    (x : genericPoints (fiber f a)) :
    AlgebraicCycle.fundamentalCycle (fiber f a) x.val =
      ∑ᶠ p : {p : PrimeSpectrum (D.presheaf.stalk (inclusion f a x.val)) //
          p.asIdeal ∈ minimalPrimes (D.presheaf.stalk (inclusion f a x.val))},
        ((Module.length (Localization.AtPrime p.val.asIdeal)
            (Localization.AtPrime p.val.asIdeal)).toNat : ℤ) *
          ((Module.length (D.presheaf.stalk (inclusion f a x.val))
            (D.presheaf.stalk (inclusion f a x.val) ⧸
              (Ideal.span {scalar f a (inclusion f a x.val)} ⊔ p.val.asIdeal))).toNat : ℤ) :=
  fundamentalCycle_apply_eq_finsum_minimalPrimes_of_regular f a x (scalar_regular f a _)

end AlgebraicGeometry.Scheme.AffineLineFiber

namespace Stacks.Chow

/-- The local minimal-prime weight is the length of the actual scheme stalk at
its actual image under `fromSpecStalk`. The comparison uses the literal
specialization stalk map, not a ring isomorphism supplied by the caller. -/
theorem length_localization_eq_length_stalk_fromSpecStalk
    {D : Scheme.{u}} (x : D) (p : PrimeSpectrum (D.presheaf.stalk x)) :
    Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) =
      Module.length (D.presheaf.stalk (D.fromSpecStalk x p))
        (D.presheaf.stalk (D.fromSpecStalk x p)) := by
  have h : D.fromSpecStalk x p ⤳ x := D.range_fromSpecStalk.subset ⟨p, rfl⟩
  let : Algebra (D.presheaf.stalk x) (D.presheaf.stalk (D.fromSpecStalk x p)) :=
    (D.presheaf.stalkSpecializes h).hom.toAlgebra
  have : IsLocalization.AtPrime (D.presheaf.stalk (D.fromSpecStalk x p)) p.asIdeal :=
    isLocalization_stalk_of_specializes h p rfl
  exact Module.length_eq_of_ringEquiv
    (IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      (D.presheaf.stalk (D.fromSpecStalk x p))).toRingEquiv

end Stacks.Chow

namespace AlgebraicGeometry.Scheme.AffineLineFiber

open Stacks.Chow

variable {k : Type u} [Field k] {D : Scheme.{u}}
  (f : D ⟶ Spec (.of (Polynomial k))) (a : k)

/-- Whole endpoint multiplicity, indexed by the actual global generic
components through the point. Every original component weight is retained.
The component ideal is the literal native integral-component stalk. -/
theorem fundamentalCycle_apply_eq_finsum_componentsThrough_of_regular [IsNoetherian D]
    (x : genericPoints (fiber f a))
    (hreg : IsSMulRegular (D.presheaf.stalk (inclusion f a x.val))
      (scalar f a (inclusion f a x.val))) :
    AlgebraicCycle.fundamentalCycle (fiber f a) x.val =
      ∑ᶠ z ∈ {z : D | z ⤳ inclusion f a x.val ∧
          ∀ z' : D, z' ⤳ z → z' = z},
        ((Module.length (D.presheaf.stalk z) (D.presheaf.stalk z)).toNat : ℤ) *
          ((Module.length (D.presheaf.stalk (inclusion f a x.val))
            (D.presheaf.stalk (inclusion f a x.val) ⧸
              (Ideal.span {scalar f a (inclusion f a x.val)} ⊔
                IdealSheafData.stalk (integralComponentAt z)
                  (inclusion f a x.val)))).toNat : ℤ) := by
  rw [fundamentalCycle_apply_eq_finsum_minimalPrimes_of_regular f a x hreg,
    finsum_componentGenericPoints_eq, ← finsum_set_coe_eq_finsum_mem]
  apply finsum_congr
  intro p
  rw [length_localization_eq_length_stalk_fromSpecStalk]
  let y := inclusion f a x.val
  let R := D.presheaf.stalk y
  let z := D.fromSpecStalk y p.val
  let c : ℤ := (Module.length (D.presheaf.stalk z) (D.presheaf.stalk z)).toNat
  have hp : IdealSheafData.stalk (integralComponentAt z) y = p.val.asIdeal :=
    idealStalk_vanishingIdeal_closure_fromSpecStalk y p.val
  exact congrArg (fun J : Ideal R =>
    c * ((Module.length R (R ⧸ (Ideal.span {scalar f a y} ⊔ J))).toNat : ℤ)) hp.symm

/-- A flat polynomial family supplies the regular cut at each endpoint. -/
theorem fundamentalCycle_apply_eq_finsum_componentsThrough [IsNoetherian D] [Flat f]
    (x : genericPoints (fiber f a)) :
    AlgebraicCycle.fundamentalCycle (fiber f a) x.val =
      ∑ᶠ z ∈ {z : D | z ⤳ inclusion f a x.val ∧
          ∀ z' : D, z' ⤳ z → z' = z},
        ((Module.length (D.presheaf.stalk z) (D.presheaf.stalk z)).toNat : ℤ) *
          ((Module.length (D.presheaf.stalk (inclusion f a x.val))
            (D.presheaf.stalk (inclusion f a x.val) ⧸
              (Ideal.span {scalar f a (inclusion f a x.val)} ⊔
                IdealSheafData.stalk (integralComponentAt z)
                  (inclusion f a x.val)))).toNat : ℤ) :=
  fundamentalCycle_apply_eq_finsum_componentsThrough_of_regular f a x (scalar_regular f a _)

end AlgebraicGeometry.Scheme.AffineLineFiber
