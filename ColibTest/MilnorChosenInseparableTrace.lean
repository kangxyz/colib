/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenInseparableTrace

/-!
Exact consumers of restriction after the native chosen norm without any prime
degree, separability, characteristic-zero, or norm tower compatibility premise.
-/

noncomputable section

open Module IntermediateField Stacks.Chow

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsPurelyInseparable K L]

example (x : MilnorKRing L) :
    milnorKRingMap (algebraMap K L) (milnorKNormRing K L x) =
      (finrank K L : ℤ) • x :=
  milnorKRingMap_milnorKNormRing_of_isPurelyInseparable x

example :
    (milnorKRingMap (algebraMap K L)).toAddMonoidHom.comp (milnorKNormRing K L) =
      (finrank K L : ℤ) • AddMonoidHom.id (MilnorKRing L) :=
  milnorKRingMap_comp_milnorKNormRing_of_isPurelyInseparable

example (n : ℕ) (x : MilnorKTheory L n) :
    milnorKTransport (algebraMap K L) n (milnorKNorm K L n x) =
      (finrank K L : ℤ) • x :=
  milnorKTransport_milnorKNorm_of_isPurelyInseparable n x

example (n : ℕ) (x : MilnorKTheory L n) :
    milnorKTheoryMap (algebraMap K L) n (milnorKNorm K L n x) =
      (finrank K L : ℤ) • x :=
  milnorKTheoryMap_milnorKNorm_of_isPurelyInseparable n x

example (n : ℕ) :
    (milnorKTransport (algebraMap K L) n).comp (milnorKNorm K L n) =
      (finrank K L : ℤ) • AddMonoidHom.id (MilnorKTheory L n) :=
  milnorKTransport_comp_milnorKNorm_of_isPurelyInseparable n

example (x : MilnorKTheory L 0) :
    milnorKTheoryMap (algebraMap K L) 0 (milnorKNorm K L 0 x) =
      (finrank K L : ℤ) • x :=
  milnorKTheoryMap_milnorKNorm_of_isPurelyInseparable 0 x

example (x : MilnorKTheory K 0) :
    milnorKTransport (algebraMap K K) 0 (milnorKNorm K K 0 x) = x := by
  simpa only [finrank_self, Nat.cast_one, one_zsmul] using
    milnorKTransport_milnorKNorm_of_isPurelyInseparable (K := K) (L := K) 0 x

example (M : IntermediateField K L) (x : MilnorKRing L) :
    milnorKRingMap (algebraMap M L) (milnorKNormRing M L x) =
      (finrank M L : ℤ) • x :=
  milnorKRingMap_milnorKNormRing_of_isPurelyInseparable x

example (M : IntermediateField K L) (x : MilnorKTheory M 2) :
    milnorKTheoryMap (algebraMap K M) 2 (milnorKNorm K M 2 x) =
      (finrank K M : ℤ) • x :=
  milnorKTheoryMap_milnorKNorm_of_isPurelyInseparable 2 x

end
