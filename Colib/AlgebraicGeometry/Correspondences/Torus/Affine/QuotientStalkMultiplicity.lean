/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# Exact local multiplicities of monic polynomial quotients

These are lengths of actual quotient modules over the native stalk of
`Spec R[X]`. A monic polynomial stays a non-zero-divisor in every stalk.
Mathlib's concrete multiplication/quotient short exact sequence therefore
proves product additivity, including repeated factors and nonreduced bases.

The unrestricted formula is `ENat`-valued. Converting lengths to integer
cycle coefficients is justified only when the stalk is Noetherian and at
most one-dimensional; the finite-length proof is retained explicitly.
No `toNat` additivity is asserted at infinite lengths.

Identifying these local equations with the closed image in the native torus
ambient scheme, and assembling its finite correspondence cycle, remains a
separate geometric step. This file does not rename these lengths as an
already constructed torus cycle.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {R : Type u} [CommRing R]

/-- The native structure-sheaf stalk of the actual affine polynomial scheme. -/
abbrev polynomialStalk (x : PrimeSpectrum R[X]) :=
  (Spec (.of R[X])).presheaf.stalk x

/-- The canonical polynomial algebra on the native affine stalk. -/
instance polynomialStalkAlgebra (x : PrimeSpectrum R[X]) :
    Algebra R[X] (polynomialStalk x) :=
  StructureSheaf.stalkAlgebra R[X] x

/-- The same canonical stalk is the localization at its actual prime. -/
instance polynomialStalkIsLocalization (x : PrimeSpectrum R[X]) :
    IsLocalization.AtPrime (polynomialStalk x) x.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk R[X] x

/-- The actual local polynomial-coordinate homomorphism into the native stalk. -/
def polynomialGerm (x : PrimeSpectrum R[X]) : R[X] →+* polynomialStalk x :=
  algebraMap R[X] (polynomialStalk x)

/-- Local multiplicity before truncation: the true native-stalk quotient length. -/
def quotientStalkLength (x : PrimeSpectrum R[X]) (p : R[X]) : ℕ∞ :=
  Module.length (polynomialStalk x)
    (polynomialStalk x ⧸ Ideal.span {polynomialGerm x p})

/-- Monicity proves local regularity even over nonreduced coefficient rings. -/
theorem polynomialGerm_mem_nonZeroDivisors (x : PrimeSpectrum R[X])
    (p : R[X]) (hp : p.Monic) :
    polynomialGerm x p ∈ nonZeroDivisors (polynomialStalk x) :=
  IsLocalization.nonZeroDivisors_le_comap x.asIdeal.primeCompl
    (polynomialStalk x) hp.mem_nonZeroDivisors

/-- Exact multiplication and quotient maps give the literal product multiplicity. -/
theorem quotientStalkLength_mul (x : PrimeSpectrum R[X])
    (p q : R[X]) (hq : q.Monic) :
    quotientStalkLength x (p * q) = quotientStalkLength x p + quotientStalkLength x q := by
  change Ring.ord (polynomialStalk x) (polynomialGerm x (p * q)) =
    Ring.ord (polynomialStalk x) (polynomialGerm x p) +
      Ring.ord (polynomialStalk x) (polynomialGerm x q)
  rw [map_mul]
  exact Ring.ord_mul _ (polynomialGerm_mem_nonZeroDivisors x q hq)

/-- Repeated factors carry their full multiplicity, without separability assumptions. -/
theorem quotientStalkLength_pow (x : PrimeSpectrum R[X])
    (p : R[X]) (hp : p.Monic) (n : ℕ) :
    quotientStalkLength x (p ^ n) = n • quotientStalkLength x p := by
  change Ring.ord (polynomialStalk x) (polynomialGerm x (p ^ n)) =
    n • Ring.ord (polynomialStalk x) (polynomialGerm x p)
  rw [map_pow]
  exact Ring.ord_pow (polynomialGerm_mem_nonZeroDivisors x p hp) n

/-- Outside the actual polynomial zero locus the quotient stalk is zero. -/
theorem quotientStalkLength_eq_zero_of_notMem (x : PrimeSpectrum R[X])
    (p : R[X]) (hp : p ∉ x.asIdeal) : quotientStalkLength x p = 0 := by
  apply Ring.ord_of_isUnit
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (polynomialStalk x) x.asIdeal p).mpr hp

/-- The unit equation has zero multiplicity at every native stalk. -/
@[simp] theorem quotientStalkLength_one (x : PrimeSpectrum R[X]) :
    quotientStalkLength x 1 = 0 := by
  change Ring.ord (polynomialStalk x) (polynomialGerm x 1) = 0
  rw [map_one, Ring.ord_one]

variable (x : PrimeSpectrum R[X])
  [IsNoetherianRing (polynomialStalk x)] [Ring.KrullDimLE 1 (polynomialStalk x)]

/-- Finiteness is proved before taking integer cycle coefficients. -/
theorem quotientStalkLength_ne_top (p : R[X]) (hp : p.Monic) :
    quotientStalkLength x p ≠ ⊤ :=
  Ring.ord_ne_top (polynomialGerm_mem_nonZeroDivisors x p hp)

/-- The integer multiplicity obtained from the actual finite local quotient length. -/
def quotientStalkMultiplicity (p : R[X]) : ℤ := (quotientStalkLength x p).toNat

/-- Integer multiplicities add for monic products, with both finiteness proofs supplied. -/
theorem quotientStalkMultiplicity_mul (p q : R[X]) (hp : p.Monic) (hq : q.Monic) :
    quotientStalkMultiplicity x (p * q) =
      quotientStalkMultiplicity x p + quotientStalkMultiplicity x q := by
  unfold quotientStalkMultiplicity
  rw [quotientStalkLength_mul x p q hq,
    ENat.toNat_add (quotientStalkLength_ne_top x p hp) (quotientStalkLength_ne_top x q hq)]
  exact Nat.cast_add _ _

/-- A repeated monic factor contributes its full integer multiplicity. -/
theorem quotientStalkMultiplicity_pow (p : R[X]) (hp : p.Monic) (n : ℕ) :
    quotientStalkMultiplicity x (p ^ n) = n • quotientStalkMultiplicity x p := by
  induction n with
  | zero => simp [quotientStalkMultiplicity]
  | succ n ih =>
    rw [pow_succ, quotientStalkMultiplicity_mul x _ _ (hp.pow n) hp, ih, succ_nsmul]

/-- Signed multiples of the true product coefficient retain the same additivity. -/
theorem zsmul_quotientStalkMultiplicity_mul
    (p q : R[X]) (hp : p.Monic) (hq : q.Monic) (n : ℤ) :
    n • quotientStalkMultiplicity x (p * q) =
      n • quotientStalkMultiplicity x p + n • quotientStalkMultiplicity x q := by
  rw [quotientStalkMultiplicity_mul x p q hp hq, smul_add]

end AlgebraicGeometry.NativeTorusPolynomial
