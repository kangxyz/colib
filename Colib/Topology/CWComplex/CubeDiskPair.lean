/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.CharacteristicPair
public import Colib.Topology.CubicalSubdivision.BoundaryLifting
public import Mathlib.Analysis.Normed.Group.Constructions

/-!
# The literal finite cube and classical characteristic disk pair

Coordinate rescaling `t ↦ 2 * t - 1` identifies the actual finite unit cube with
Mathlib's sup-norm characteristic disk. Its restriction identifies the entire
cube boundary with the literal unit sphere and commutes with both inclusions.
Dimension zero is included: the disk is a singleton and both boundaries are empty.

`BoundaryLifting.characteristicDisk` transports strict cubical boundary lifting
to these original disk coordinates. The supplied sphere map is preserved
pointwise; no replacement of the boundary map or characteristic map is made.

Adapted from `Quillen/Topology/CWComplex/CubeDiskPair.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

open Topology

noncomputable section
open Set Metric
open scoped unitInterval
universe u v
namespace Topology.CWComplex

/-- Rescale each original coordinate, with inverse `x ↦ (x + 1) / 2`. -/
def cubeDiskHomeomorph (n : ℕ) : CubicalSubdivision.Cube n ≃ₜ CharacteristicDisk n where
  toFun t := ⟨fun i ↦ 2 * (t i : ℝ) - 1, by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
    intro i
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(t i).property.1, (t i).property.2]⟩
  invFun x i := ⟨(x.val i + 1) / 2, by
    have hi : ‖x.val i‖ ≤ 1 :=
      (norm_le_pi_norm x.val i).trans (mem_closedBall_zero_iff.mp x.property)
    rw [Real.norm_eq_abs, abs_le] at hi
    constructor <;> linarith [hi.1, hi.2]⟩
  left_inv t := by
    funext i
    apply Subtype.ext
    change (2 * (t i : ℝ) - 1 + 1) / 2 = (t i : ℝ)
    ring
  right_inv x := by
    apply Subtype.ext
    funext i
    change 2 * ((x.val i + 1) / 2) - 1 = x.val i
    ring
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro i
    exact ((((continuous_apply i).comp continuous_subtype_val).add_const 1).div_const
      2).subtype_mk _

@[simp] theorem cubeDiskHomeomorph_apply (n : ℕ) (t : CubicalSubdivision.Cube n)
    (i : Fin n) : (cubeDiskHomeomorph n t).val i = 2 * (t i : ℝ) - 1 := rfl

@[simp] theorem cubeDiskHomeomorph_symm_apply (n : ℕ) (x : CharacteristicDisk n)
    (i : Fin n) : ((cubeDiskHomeomorph n).symm x i : ℝ) = (x.val i + 1) / 2 := rfl

/-- The literal cube boundary is carried exactly onto the literal sphere.
The proof uses finite sup-norm inequalities and also applies when `n = 0`. -/
theorem cubeDiskHomeomorph_mem_sphere_iff (n : ℕ) (t : CubicalSubdivision.Cube n) :
    (cubeDiskHomeomorph n t).val ∈ sphere (0 : Fin n → ℝ) 1 ↔
      t ∈ _root_.Cube.boundary (Fin n) := by
  rw [mem_sphere_zero_iff_norm]
  constructor
  · intro ht
    by_contra hb
    have hlt : ‖(cubeDiskHomeomorph n t).val‖ < 1 := by
      rw [pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
      intro i
      have hzero : (t i : ℝ) ≠ 0 := by
        intro hi
        exact hb ⟨i, Or.inl (Subtype.ext hi)⟩
      have hone : (t i : ℝ) ≠ 1 := by
        intro hi
        exact hb ⟨i, Or.inr (Subtype.ext hi)⟩
      have hpos : 0 < (t i : ℝ) := lt_of_le_of_ne (t i).property.1 hzero.symm
      have hltone : (t i : ℝ) < 1 := lt_of_le_of_ne (t i).property.2 hone
      rw [cubeDiskHomeomorph_apply, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    exact (ne_of_lt hlt) ht
  · rintro ⟨i, hi⟩
    apply le_antisymm (mem_closedBall_zero_iff.mp (cubeDiskHomeomorph n t).property)
    have hle := norm_le_pi_norm (cubeDiskHomeomorph n t).val i
    rcases hi with hi | hi
    · simpa only [cubeDiskHomeomorph_apply, hi, Set.Icc.coe_zero, mul_zero,
        zero_sub, norm_neg, norm_one] using hle
    · simpa only [cubeDiskHomeomorph_apply, hi, Set.Icc.coe_one, mul_one,
        show (2 : ℝ) - 1 = 1 by norm_num, norm_one] using hle

/-- Restrict coordinate rescaling to the entire original boundary. -/
def cubeBoundarySphereHomeomorph (n : ℕ) :
    CubicalSubdivision.Boundary n ≃ₜ CharacteristicSphere n where
  toFun t := ⟨(cubeDiskHomeomorph n t.val).val,
    (cubeDiskHomeomorph_mem_sphere_iff n t.val).mpr t.property⟩
  invFun z := ⟨(cubeDiskHomeomorph n).symm (characteristicSphereInclusion n z), by
    apply (cubeDiskHomeomorph_mem_sphere_iff n _).mp
    simpa only [Homeomorph.apply_symm_apply, characteristicSphereInclusion_val]
      using z.property⟩
  left_inv t := by
    apply Subtype.ext
    exact (cubeDiskHomeomorph n).symm_apply_apply t.val
  right_inv z := by
    apply Subtype.ext
    change (cubeDiskHomeomorph n
      ((cubeDiskHomeomorph n).symm (characteristicSphereInclusion n z))).val = z.val
    exact congrArg Subtype.val
      ((cubeDiskHomeomorph n).apply_symm_apply (characteristicSphereInclusion n z))
  continuous_toFun := (continuous_subtype_val.comp
    ((cubeDiskHomeomorph n).continuous.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := ((cubeDiskHomeomorph n).symm.continuous.comp
    (characteristicSphereInclusion n).continuous).subtype_mk _

/-- The forward pair square commutes on the original coordinates. -/
@[simp] theorem cubeBoundarySphereHomeomorph_inclusion (n : ℕ)
    (t : CubicalSubdivision.Boundary n) :
    characteristicSphereInclusion n (cubeBoundarySphereHomeomorph n t) =
      cubeDiskHomeomorph n t.val := rfl

/-- The inverse pair square also commutes on the original coordinates. -/
@[simp] theorem cubeBoundarySphereHomeomorph_symm_val (n : ℕ)
    (z : CharacteristicSphere n) :
    ((cubeBoundarySphereHomeomorph n).symm z).val =
      (cubeDiskHomeomorph n).symm (characteristicSphereInclusion n z) := rfl

/-- The original zero-dimensional cube boundary is empty as well. -/
theorem cubeBoundary_zero_isEmpty : IsEmpty (CubicalSubdivision.Boundary 0) := by
  constructor
  rintro ⟨_, i, _⟩
  exact Fin.elim0 i

end Topology.CWComplex

namespace Topology.CubicalSubdivision
open Topology.CWComplex

/-- Strict cubical lifting gives an exact lift on every original characteristic
disk, retaining the supplied sphere map pointwise, including dimension zero. -/
theorem BoundaryLifting.characteristicDisk
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (hp : BoundaryLifting p) (n : ℕ)
    (a : C(CharacteristicSphere n, E)) (b : C(CharacteristicDisk n, B))
    (hab : ∀ z, p (a z) = b (characteristicSphereInclusion n z)) :
    ∃ c : C(CharacteristicDisk n, E),
      (∀ z, c (characteristicSphereInclusion n z) = a z) ∧ p.comp c = b := by
  let e := cubeDiskHomeomorph n
  let d := cubeBoundarySphereHomeomorph n
  let a' := a.comp d.toHomotopyEquiv.toFun
  let b' := b.comp e.toHomotopyEquiv.toFun
  have h : ∀ t : Boundary n, p (a' t) = b' t := fun t ↦ hab (d t)
  obtain ⟨c, hc, he⟩ := hp n a' b' h
  refine ⟨c.comp e.symm.toHomotopyEquiv.toFun, ?_, ?_⟩
  · intro z
    have hz := hc (d.symm z)
    change c (e.symm (characteristicSphereInclusion n z)) = a (d (d.symm z)) at hz
    change c (e.symm (characteristicSphereInclusion n z)) = a z
    simpa only [Homeomorph.apply_symm_apply] using hz
  · apply ContinuousMap.ext
    intro z
    have hz := ContinuousMap.congr_fun he (e.symm z)
    change p (c (e.symm z)) = b (e (e.symm z)) at hz
    change p (c (e.symm z)) = b z
    simpa only [Homeomorph.apply_symm_apply] using hz

end Topology.CubicalSubdivision
