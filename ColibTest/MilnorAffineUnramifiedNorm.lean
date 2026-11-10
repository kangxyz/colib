/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Dedekind.AffineUnramifiedNorm

/-! Consumers of the affine unramified norm theorem. -/

noncomputable section
open Polynomial Stacks.Chow Stacks.Chow.DedekindResidue

universe u
variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

example (n : ℕ) (x : MilnorKTheory E (n + 1)) (hx : totalResidue S E n x = 0) :
    milnorKNorm (RatFunc k) E (n + 1) x ∈
      LinearMap.range (milnorKTheoryMap (RatFunc.C : k →+* RatFunc k) (n + 1)) :=
  norm_mem_constant_range_of_totalResidue_zero k S E n x hx

example (x : MilnorKTheory E 1) (hx : totalResidue S E 0 x = 0) :
    milnorKNorm (RatFunc k) E 1 x ∈
      LinearMap.range (milnorKTheoryMap (RatFunc.C : k →+* RatFunc k) 1) :=
  norm_mem_constant_range_of_totalResidue_zero k S E 0 x hx

example (n : ℕ) (a : Fin (n + 1) → Sˣ) :
    totalResidue S E n
      (milnorKTupleSymbol (Units.map (algebraMap S E).toMonoidHom ∘ a)) = 0 :=
  totalResidue_ring_units S E n a

example (n : ℕ) (a : Fin (n + 1) → Sˣ) :
    milnorKNorm (RatFunc k) E (n + 1)
      (milnorKTupleSymbol (Units.map (algebraMap S E).toMonoidHom ∘ a)) ∈
      LinearMap.range (milnorKTheoryMap (RatFunc.C : k →+* RatFunc k) (n + 1)) :=
  norm_ring_unit_symbol_mem_constant_range k S E n a
