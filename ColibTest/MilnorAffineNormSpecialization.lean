/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Dedekind.AffineNormSpecialization

/-! Consumers of the native linear-place norm specialization. -/

noncomputable section
open Polynomial Stacks.Chow Stacks.Chow.PolynomialResidue

section Constants
variable (k : Type*) [Field k]

example (a : k) (n : ℕ) :
    (linearSpecialization a n).comp
      (milnorKTheoryMap (RatFunc.C : k →+* RatFunc k) n) = LinearMap.id :=
  linearSpecialization_comp_constants a n

example (a : k) (x : MilnorKTheory k 0) :
    linearSpecialization a 0 (milnorKTheoryMap (RatFunc.C : k →+* RatFunc k) 0 x) = x :=
  linearSpecialization_constants a 0 x

example (a : k) (n : ℕ) (x : MilnorKTheory k n) :
    linearResidue a n
      (milnorKMulSymbol (RatFunc k) n (polyUnit (irreducible_X_sub_C a).ne_zero)
        (milnorKTheoryMap (RatFunc.C : k →+* RatFunc k) n x)) = x :=
  linearResidue_mulSymbol_constants a n x

end Constants

universe u
open Stacks.Chow.DedekindResidue
variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

example (a b : k) (n : ℕ) (x : MilnorKTheory E (n + 1))
    (hx : totalResidue S E n x = 0) :
    linearSpecialization a (n + 1) (milnorKNorm (RatFunc k) E (n + 1) x) =
      linearSpecialization b (n + 1) (milnorKNorm (RatFunc k) E (n + 1) x) :=
  linearSpecialization_norm_eq_of_totalResidue_zero k S E a b n x hx
