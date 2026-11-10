/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Dedekind.PolynomialTotalNorm

/-! Consumers of the native prime residue comparison. -/

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.PolynomialDedekindResidue
open MonicIrreducibleOfDegree IsDedekindDomain

attribute [local instance] Ideal.Quotient.field

universe u
variable (k : Type u) [Field k]

example (q : HeightOneSpectrum k[X]) : point (polynomial q) = q := point_polynomial q

example (p : MonicIrreduciblePoint k) :
    DedekindResidue.fractionAlgebra k[X] (RatFunc k) (point p) =
      algebraLocalizationAtPrimeRatFunc (Ideal.span {poly p.2}) :=
  fractionAlgebra_eq p

example (p : MonicIrreduciblePoint k) (n : ℕ)
    (x : MilnorKTheory (RatFunc k) (n + 1)) :
    milnorKTransport (quotientRingEquivResidueField (Ideal.span {poly p.2})).symm.toRingHom n
      (DedekindResidue.totalResidue k[X] (RatFunc k) n x (point p)) =
        milnorKTotalResidue k n x p :=
  totalResidue_point p n x

example (p : MonicIrreduciblePoint k) (x : MilnorKTheory (RatFunc k) 1) :
    milnorKTransport (quotientRingEquivResidueField (Ideal.span {poly p.2})).symm.toRingHom 0
      (DedekindResidue.totalResidue k[X] (RatFunc k) 0 x (point p)) =
        milnorKTotalResidue k 0 x p :=
  totalResidue_point p 0 x

variable [CharZero k]

example (p : MonicIrreduciblePoint k) (n : ℕ)
    (x : MilnorKTheory (RatFunc k) (n + 1)) :
    (milnorKNorm k (IsLocalRing.ResidueField (Localization.AtPrime (point p).asIdeal)) n
      (DedekindResidue.totalResidue k[X] (RatFunc k) n x (point p)) : MilnorKRing k) =
      simpleMilnorNorm p.2 (milnorKTotalResidue k n x p) :=
  norm_totalResidue_point k p n x

example (x : MilnorKTheory (RatFunc k) 1) :
    DedekindResidue.normedTotalResidue k k[X] (RatFunc k) 0 x +
      infinityResidue (k := k) 0 x = 0 :=
  normedTotalResidue_add_infinity k 0 x
