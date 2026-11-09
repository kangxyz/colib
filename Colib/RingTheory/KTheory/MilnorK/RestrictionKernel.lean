/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FieldNorm
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Finite restriction kernels on native Milnor K-theory

The projection formula for the actual native chosen norm kills the kernel of
finite restriction by the field degree. This works in arbitrary characteristic,
without separability or presentation independence. Coprime-order torsion and
two restrictions of coprime degrees are consequently detected on the original
Milnor ring and each original homogeneous group, including degree zero.

This adapts the restriction-kernel argument in `Aglib/KTheory/MilnorK/RestrictionKernel.lean`
at revision `52e09db47998f139064acf48a2d3a64494d0dd9a`. The native chosen norm replaces
that source's auxiliary primitive-element retraction, removing its separability
hypothesis. No new transfer or norm tower compatibility is asserted.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Chow

variable (k E : Type u) [Field k] [Field E] [Algebra k E] [FiniteDimensional k E]

/-- Native norm after native restriction is multiplication by the extension
degree on each homogeneous group. -/
theorem milnorKNorm_milnorKTransport (n : ℕ) (x : MilnorKTheory k n) :
    milnorKNorm k E n (milnorKTransport (algebraMap k E) n x) =
      (Module.finrank k E : ℤ) • x := by
  apply Subtype.ext
  exact milnorKNormRing_milnorKRingMap (x : MilnorKRing k)

/-- The kernel of finite restriction on the whole native ring is killed by the
actual field degree. Inseparable extensions are included. -/
theorem finrank_zsmul_eq_zero_of_milnorKRingMap_eq_zero (x : MilnorKRing k)
    (hx : milnorKRingMap (algebraMap k E) x = 0) :
    (Module.finrank k E : ℤ) • x = 0 := by
  rw [← milnorKNormRing_milnorKRingMap (K := k) (L := E) x, hx, map_zero]

/-- Finite restriction kernels in every native homogeneous degree are killed by
the degree of the extension, without separability. -/
theorem finrank_zsmul_eq_zero_of_milnorKTransport_eq_zero (n : ℕ)
    (x : MilnorKTheory k n) (hx : milnorKTransport (algebraMap k E) n x = 0) :
    (Module.finrank k E : ℤ) • x = 0 := by
  rw [← milnorKNorm_milnorKTransport k E n x, hx, map_zero]

/-- Finite restriction detects a class killed by an integer coprime to the
extension degree. It need not be injective on arbitrary classes. -/
theorem eq_zero_of_milnorKRingMap_eq_zero_of_coprime (m : ℕ)
    (hm : m.Coprime (Module.finrank k E)) (x : MilnorKRing k)
    (hx : milnorKRingMap (algebraMap k E) x = 0) (hxm : (m : ℤ) • x = 0) : x = 0 := by
  obtain ⟨a, b, hab⟩ := hm.isCoprime
  have hd := finrank_zsmul_eq_zero_of_milnorKRingMap_eq_zero k E x hx
  calc
    x = (1 : ℤ) • x := (one_smul ℤ x).symm
    _ = (a * m + b * (Module.finrank k E : ℤ)) • x := by rw [hab]
    _ = 0 := by
      rw [add_smul, mul_smul, mul_smul, hxm, hd, smul_zero, smul_zero, add_zero]

/-- Coprime-order detection on the original homogeneous Milnor group. -/
theorem eq_zero_of_milnorKTransport_eq_zero_of_coprime (n m : ℕ)
    (hm : m.Coprime (Module.finrank k E)) (x : MilnorKTheory k n)
    (hx : milnorKTransport (algebraMap k E) n x = 0) (hxm : (m : ℤ) • x = 0) : x = 0 := by
  apply Subtype.ext
  exact eq_zero_of_milnorKRingMap_eq_zero_of_coprime k E m hm (x : MilnorKRing k)
    (congrArg Subtype.val hx) (congrArg Subtype.val hxm)

/-- A prime-to-`p` finite extension detects `p`-power torsion in every degree.
The arithmetic statement does not require that `p` is prime. -/
theorem eq_zero_of_milnorKTransport_eq_zero_of_coprime_pow (n p r : ℕ)
    (hp : p.Coprime (Module.finrank k E)) (x : MilnorKTheory k n)
    (hx : milnorKTransport (algebraMap k E) n x = 0)
    (hxp : ((p ^ r : ℕ) : ℤ) • x = 0) : x = 0 :=
  eq_zero_of_milnorKTransport_eq_zero_of_coprime k E n (p ^ r) (hp.pow_left r) x hx hxp

/-- Two finite restrictions of coprime degrees jointly detect a native ring
class. The two extensions need not belong to a tower. -/
theorem eq_zero_of_two_milnorKRingMaps_eq_zero_of_coprime
    (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L]
    (hEL : (Module.finrank k E).Coprime (Module.finrank k L)) (x : MilnorKRing k)
    (hE : milnorKRingMap (algebraMap k E) x = 0)
    (hL : milnorKRingMap (algebraMap k L) x = 0) : x = 0 :=
  eq_zero_of_milnorKRingMap_eq_zero_of_coprime k L (Module.finrank k E) hEL x hL
    (finrank_zsmul_eq_zero_of_milnorKRingMap_eq_zero k E x hE)

/-- Two coprime-degree restrictions jointly detect every native homogeneous
class, including degree zero. -/
theorem eq_zero_of_two_milnorKTransports_eq_zero_of_coprime
    (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L]
    (hEL : (Module.finrank k E).Coprime (Module.finrank k L)) (n : ℕ)
    (x : MilnorKTheory k n) (hE : milnorKTransport (algebraMap k E) n x = 0)
    (hL : milnorKTransport (algebraMap k L) n x = 0) : x = 0 :=
  eq_zero_of_milnorKTransport_eq_zero_of_coprime k L n (Module.finrank k E) hEL x hL
    (finrank_zsmul_eq_zero_of_milnorKTransport_eq_zero k E n x hE)

end Stacks.Chow
