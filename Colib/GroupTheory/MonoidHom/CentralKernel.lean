/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.GroupTheory.MonoidHom.CentralLifts
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Commutators across a central kernel

Adapted from `Quillen/Aglib/Algebra/Group/Hom/CentralKernel.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Commutators depend only on the
projected pair. A conjugation can also compare a commutator with a specified
lift by varying both lifts by multiplication.

-/

@[expose] public section

namespace MonoidHom.CentralKernel

open scoped commutatorElement

variable {E G H : Type*} [Group E] [Group G] [Group H]

/-- If a conjugation fixes `b` and multiplies `x` and a lift of `⁅x,b⁆`
by `a` and `c` respectively, the central difference cancels and `⁅a,b⁆ = c`. -/
theorem commutator_eq_of_conjugation_mul (p : E →* G) (hcentral : p.ker ≤ Subgroup.center E)
    {a b c x y d : E} (hproj : p ⁅x, b⁆ = p y) (hay : Commute a y)
    (hx : d * x * d⁻¹ = a * x) (hb : d * b * d⁻¹ = b)
    (hy : d * y * d⁻¹ = y * c) : ⁅a, b⁆ = c := by
  let z := ⁅x, b⁆ * y⁻¹
  have hz : z ∈ Subgroup.center E := hcentral (by
    simp only [z, MonoidHom.mem_ker, map_mul, map_inv, hproj, mul_inv_cancel])
  have hzy : z * y = ⁅x, b⁆ := by simp [z, mul_assoc]
  have hcomm : Commute a ⁅x, b⁆ := by
    rw [← hzy]
    exact (show Commute a z from Subgroup.mem_center_iff.mp hz a).mul_right hay
  have hfix : d * z * d⁻¹ = z := by
    rw [Subgroup.mem_center_iff.mp hz d, mul_inv_cancel_right]
  apply mul_left_cancel (a := ⁅x, b⁆)
  calc
    _ = ⁅a * x, b⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, hcomm.eq, mul_inv_cancel_right]
    _ = d * ⁅x, b⁆ * d⁻¹ := by rw [conjugate_commutatorElement, hx, hb]
    _ = (d * z * d⁻¹) * (d * y * d⁻¹) := by
      rw [← hzy]
      simp only [mul_assoc, inv_mul_cancel_left]
    _ = _ := by rw [hfix, hy, ← mul_assoc, hzy]

/-- Commutators depend only on the two projected elements when the kernel is central. -/
theorem commutator_eq_of_projection_eq (p : E →* G) (hcentral : p.ker ≤ Subgroup.center E)
    {x x' y y' : E} (hx : p x = p x') (hy : p y = p y') : ⁅x, y⁆ = ⁅x', y'⁆ := by
  have hz : x'⁻¹ * x ∈ Subgroup.center E := hcentral (by
    change p (x'⁻¹ * x) = 1
    rw [map_mul, map_inv, hx, inv_mul_cancel])
  have hw : y'⁻¹ * y ∈ Subgroup.center E := hcentral (by
    change p (y'⁻¹ * y) = 1
    rw [map_mul, map_inv, hy, inv_mul_cancel])
  have hzy : Commute (x'⁻¹ * x) y :=
    (show Commute y (x'⁻¹ * x) from (Subgroup.mem_center_iff.mp hz) y).symm
  have hxw : Commute x' (y'⁻¹ * y) := (Subgroup.mem_center_iff.mp hw) x'
  calc
    ⁅x, y⁆ = ⁅x' * (x'⁻¹ * x), y⁆ := by simp
    _ = ⁅x', y⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, hzy.commutator_eq]
      simp
    _ = ⁅x', y' * (y'⁻¹ * y)⁆ := by simp
    _ = ⁅x', y'⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hxw.commutator_eq]
      simp

/-- Actual torus lifts can replace projected root words when computing their commutator. -/
theorem commutator_eq_torus_commutator (p : E →* G)
    (hcentral : p.ker ≤ Subgroup.center E) (τ : H →* E)
    {x y : E} {a b : H} (hx : p x = p (τ a)) (hy : p y = p (τ b)) :
    ⁅x, y⁆ = τ ⁅a, b⁆ := by
  rw [commutator_eq_of_projection_eq p hcentral hx hy]
  exact (map_commutatorElement τ a b).symm

end MonoidHom.CentralKernel
