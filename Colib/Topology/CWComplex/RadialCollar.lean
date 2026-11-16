/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.CharacteristicPair
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Topology.Homotopy.Basic

/-!
# Radial collars in the original characteristic disk

The collar over a subset of the literal sup-norm sphere consists of disk points
of norm greater than one half whose radial direction belongs to that subset.
The radial deformation fixes the sphere and preserves the radial direction.
There is no positive-dimension hypothesis: the zero-dimensional annulus, and
therefore every zero-dimensional collar, is empty.

This is the elementary disk geometry used in the skeletal neighborhood
construction of Hatcher, *Algebraic Topology*, Appendix, Proposition A.4.

Adapted from `Quillen/Topology/CWComplex/RadialCollar.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

open Topology
noncomputable section
open Set Metric
open scoped unitInterval
namespace Topology.CWComplex

/-- The relatively open outer half of the original closed characteristic disk. -/
def characteristicAnnulusSet (n : ℕ) : Set (CharacteristicDisk n) :=
  {z | (1 / 2 : ℝ) < ‖z.val‖}

/-- The annulus carries its actual subspace topology. -/
abbrev CharacteristicAnnulus (n : ℕ) := ↥(characteristicAnnulusSet n)

theorem isOpen_characteristicAnnulusSet (n : ℕ) :
    IsOpen (characteristicAnnulusSet n) :=
  isOpen_lt continuous_const continuous_subtype_val.norm

theorem characteristicAnnulus_norm_pos {n : ℕ} (z : CharacteristicAnnulus n) :
    0 < ‖z.val.val‖ := lt_trans (by norm_num) z.property

theorem characteristicAnnulus_norm_le_one {n : ℕ} (z : CharacteristicAnnulus n) :
    ‖z.val.val‖ ≤ 1 := mem_closedBall_zero_iff.mp z.val.property

/-- Normalization in the original real coordinates, with a proved nonzero norm. -/
def radialDirection (n : ℕ) : C(CharacteristicAnnulus n, CharacteristicSphere n) where
  toFun z := ⟨‖z.val.val‖⁻¹ • z.val.val, by
    rw [mem_sphere_zero_iff_norm,
      norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (characteristicAnnulus_norm_pos z).ne']⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (((continuous_subtype_val.comp continuous_subtype_val).norm.inv₀
      (fun z ↦ (characteristicAnnulus_norm_pos z).ne')).smul
      (continuous_subtype_val.comp continuous_subtype_val))

/-- The literal sphere sits inside the outer annulus. -/
def sphereToAnnulus (n : ℕ) : C(CharacteristicSphere n, CharacteristicAnnulus n) where
  toFun z := ⟨characteristicSphereInclusion n z, by
    change (1 / 2 : ℝ) < ‖z.val‖
    rw [mem_sphere_zero_iff_norm.mp z.property]
    norm_num⟩
  continuous_toFun := (characteristicSphereInclusion n).continuous.subtype_mk _

@[simp] theorem radialDirection_sphereToAnnulus (n : ℕ) (z : CharacteristicSphere n) :
    radialDirection n (sphereToAnnulus n z) = z := by
  apply Subtype.ext
  change ‖z.val‖⁻¹ • z.val = z.val
  rw [mem_sphere_zero_iff_norm.mp z.property, inv_one, one_smul]

/-- The coefficient in the outward radial deformation. -/
def radialCoefficient {n : ℕ} (t : I) (z : CharacteristicAnnulus n) : ℝ :=
  (1 - (t : ℝ)) + (t : ℝ) / ‖z.val.val‖

theorem radialCoefficient_nonneg {n : ℕ} (t : I) (z : CharacteristicAnnulus n) :
    0 ≤ radialCoefficient t z :=
  add_nonneg (sub_nonneg.mpr t.property.2)
    (div_nonneg t.property.1 (norm_nonneg _))

theorem radialCoefficient_mul_norm {n : ℕ} (t : I) (z : CharacteristicAnnulus n) :
    radialCoefficient t z * ‖z.val.val‖ =
      (1 - (t : ℝ)) * ‖z.val.val‖ + (t : ℝ) := by
  rw [radialCoefficient, add_mul, div_mul_cancel₀ _ (characteristicAnnulus_norm_pos z).ne']

theorem radialCoefficient_norm_bounds {n : ℕ} (t : I) (z : CharacteristicAnnulus n) :
    (1 / 2 : ℝ) < ‖radialCoefficient t z • z.val.val‖ ∧
      ‖radialCoefficient t z • z.val.val‖ ≤ 1 := by
  rw [norm_smul_of_nonneg (radialCoefficient_nonneg t z), radialCoefficient_mul_norm]
  have hz : (1 / 2 : ℝ) < ‖z.val.val‖ := z.property
  have hr := characteristicAnnulus_norm_le_one z
  have ht₀ : 0 ≤ (t : ℝ) := t.property.1
  have ht₁ : (t : ℝ) ≤ 1 := t.property.2
  constructor <;> nlinarith [mul_nonneg ht₀ (sub_nonneg.mpr hr),
    mul_nonneg (sub_nonneg.mpr ht₁) (sub_nonneg.mpr hr)]

/-- Radially move each annulus point to its own sphere point. -/
def annulusRadialMap (n : ℕ) : C(I × CharacteristicAnnulus n, CharacteristicAnnulus n) where
  toFun p := ⟨⟨radialCoefficient p.1 p.2 • p.2.val.val,
    mem_closedBall_zero_iff.mpr (radialCoefficient_norm_bounds p.1 p.2).2⟩,
    (radialCoefficient_norm_bounds p.1 p.2).1⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have ht : Continuous (fun p : I × CharacteristicAnnulus n ↦ (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hz : Continuous (fun p : I × CharacteristicAnnulus n ↦ p.2.val.val) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    exact ((continuous_const.sub ht).add
      (ht.div hz.norm (fun p ↦ (characteristicAnnulus_norm_pos p.2).ne'))).smul hz

@[simp] theorem annulusRadialMap_zero (n : ℕ) (z : CharacteristicAnnulus n) :
    annulusRadialMap n (0, z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  simp [annulusRadialMap, radialCoefficient]

@[simp] theorem annulusRadialMap_one (n : ℕ) (z : CharacteristicAnnulus n) :
    annulusRadialMap n (1, z) = sphereToAnnulus n (radialDirection n z) := by
  apply Subtype.ext
  apply Subtype.ext
  simp [annulusRadialMap, radialCoefficient, sphereToAnnulus, radialDirection]

@[simp] theorem annulusRadialMap_sphere (n : ℕ) (t : I) (z : CharacteristicSphere n) :
    annulusRadialMap n (t, sphereToAnnulus n z) = sphereToAnnulus n z := by
  apply Subtype.ext
  apply Subtype.ext
  change (((1 - (t : ℝ)) + (t : ℝ) / ‖z.val‖) • z.val) = z.val
  rw [mem_sphere_zero_iff_norm.mp z.property, div_one,
    sub_add_cancel, one_smul]

/-- Direction is preserved at every time, not just at the two endpoints. -/
@[simp] theorem radialDirection_annulusRadialMap (n : ℕ) (t : I)
    (z : CharacteristicAnnulus n) :
    radialDirection n (annulusRadialMap n (t, z)) = radialDirection n z := by
  apply Subtype.ext
  change ‖radialCoefficient t z • z.val.val‖⁻¹ •
    (radialCoefficient t z • z.val.val) = ‖z.val.val‖⁻¹ • z.val.val
  rw [norm_smul_of_nonneg (radialCoefficient_nonneg t z), smul_smul]
  congr 1
  have hr : ‖z.val.val‖ ≠ 0 := (characteristicAnnulus_norm_pos z).ne'
  have hc : radialCoefficient t z ≠ 0 := by
    intro hc
    have h := (radialCoefficient_norm_bounds t z).1
    rw [hc, zero_smul, norm_zero] at h
    norm_num at h
  field_simp

/-- The actual collar as a subset of the original disk, not an abstract replacement. -/
def radialCollarSet (n : ℕ) (V : Set (CharacteristicSphere n)) :
    Set (CharacteristicDisk n) :=
  Subtype.val '' ((radialDirection n) ⁻¹' V)

/-- Collar points keep their annulus witness and their literal radial direction. -/
abbrev RadialCollar (n : ℕ) (V : Set (CharacteristicSphere n)) :=
  ↥((radialDirection n) ⁻¹' V)

theorem isOpen_radialCollarSet (n : ℕ) {V : Set (CharacteristicSphere n)}
    (hV : IsOpen V) : IsOpen (radialCollarSet n V) :=
  (isOpen_characteristicAnnulusSet n).isOpenMap_subtype_val _
    (hV.preimage (radialDirection n).continuous)

theorem mem_radialCollarSet_iff (n : ℕ) (V : Set (CharacteristicSphere n))
    (z : CharacteristicDisk n) :
    z ∈ radialCollarSet n V ↔
      ∃ h : (1 / 2 : ℝ) < ‖z.val‖, radialDirection n ⟨z, h⟩ ∈ V := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · rintro ⟨h, hh⟩
    exact ⟨⟨z, h⟩, hh, rfl⟩

/-- The collar meets the sphere in exactly the supplied subset. -/
@[simp] theorem sphere_mem_radialCollarSet (n : ℕ)
    (V : Set (CharacteristicSphere n)) (z : CharacteristicSphere n) :
    characteristicSphereInclusion n z ∈ radialCollarSet n V ↔ z ∈ V := by
  rw [mem_radialCollarSet_iff]
  constructor
  · rintro ⟨h, hh⟩
    have he : (⟨characteristicSphereInclusion n z, h⟩ : CharacteristicAnnulus n) =
        sphereToAnnulus n z := Subtype.ext rfl
    simpa only [he, radialDirection_sphereToAnnulus] using hh
  · intro hz
    refine ⟨(sphereToAnnulus n z).property, ?_⟩
    change radialDirection n (sphereToAnnulus n z) ∈ V
    simpa only [radialDirection_sphereToAnnulus] using hz

/-- The collar's inclusion in the original disk. -/
def collarDiskInclusion (n : ℕ) (V : Set (CharacteristicSphere n)) :
    C(RadialCollar n V, CharacteristicDisk n) :=
  ⟨fun z ↦ z.val.val, continuous_subtype_val.comp continuous_subtype_val⟩

/-- The restricted radial deformation stays in the same collar. -/
def collarRadialMap (n : ℕ) (V : Set (CharacteristicSphere n)) :
    C(I × RadialCollar n V, RadialCollar n V) where
  toFun p := ⟨annulusRadialMap n (p.1, p.2.val), by
    change radialDirection n (annulusRadialMap n (p.1, p.2.val)) ∈ V
    rw [radialDirection_annulusRadialMap]
    exact p.2.property⟩
  continuous_toFun := ((annulusRadialMap n).continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

@[simp] theorem collarRadialMap_zero (n : ℕ) (V : Set (CharacteristicSphere n))
    (z : RadialCollar n V) : collarRadialMap n V (0, z) = z := by
  apply Subtype.ext
  exact annulusRadialMap_zero n z.val

/-- Normalization cannot create a sphere point in dimension zero. -/
theorem characteristicAnnulus_zero_isEmpty : IsEmpty (CharacteristicAnnulus 0) := by
  let := characteristicSphere_zero_isEmpty
  exact Function.isEmpty (radialDirection 0)

theorem radialCollar_zero_isEmpty (V : Set (CharacteristicSphere 0)) :
    IsEmpty (RadialCollar 0 V) := by
  let := characteristicAnnulus_zero_isEmpty
  infer_instance

@[simp] theorem radialCollarSet_zero (V : Set (CharacteristicSphere 0)) :
    radialCollarSet 0 V = ∅ := by
  let := characteristicAnnulus_zero_isEmpty
  ext z
  simp [radialCollarSet]

@[simp] theorem radialCollarSet_empty (n : ℕ) : radialCollarSet n ∅ = ∅ := by
  simp [radialCollarSet]

end Topology.CWComplex
