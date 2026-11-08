/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenLongExactSequence
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The actual supported degree-zero restriction image

For every native open immersion and auxiliary support open, relative K0
maps onto exactly the image of the actual supported restriction. The
quotient-image comparison and literal original-map equations hold without
compactness or separation. Adapted from Quillen SupportedOpen/KZeroImage.lean
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Full-target surjectivity remains precisely the
surjectivity of that actual supported restriction.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The relative endpoint sees exactly the original extendible K-zero subgroup. -/
theorem range_perfectSupportedOpenKRestrict_zero :
    (perfectSupportedOpenKRestrict j T 0).range = (perfectSupportedKRestrict j T 0).range := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := perfectSupportedOpenKMap_zero_surjective j T a
    exact ⟨b, (DFunLike.congr_fun (perfectSupportedOpenKRestrict_comp_perfectSupportedOpenKMap j T
      0) b).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨perfectSupportedOpenKMap j T 0 a, DFunLike.congr_fun
      (perfectSupportedOpenKRestrict_comp_perfectSupportedOpenKMap j T 0) a⟩

/-- The honest degree-zero target is the actual subgroup of extendible classes. -/
abbrev PerfectSupportedOpenKZeroImage := (perfectSupportedKRestrict j T 0).range

/-- The original relative restriction, with only its codomain restricted to its actual image. -/
def perfectSupportedOpenKZeroToImage :
    PerfectSupportedOpenCoarseK j T 0 →* PerfectSupportedOpenKZeroImage
  j T :=
  (perfectSupportedOpenKRestrict j T 0).codRestrict (PerfectSupportedOpenKZeroImage j T)
    (fun a ↦ by
      change perfectSupportedOpenKRestrict j T 0 a ∈ (perfectSupportedKRestrict j T 0).range
      rw [← range_perfectSupportedOpenKRestrict_zero j]
      exact ⟨a, rfl⟩)

/-- Forgetting subgroup membership recovers the literal original relative restriction. -/
@[simp] theorem perfectSupportedOpenKZeroToImage_coe (a : PerfectSupportedOpenCoarseK j T 0) :
    (perfectSupportedOpenKZeroToImage j T a : PerfectSupportedK (j ⁻¹ᵁ T).ι 0) =
      perfectSupportedOpenKRestrict j T 0 a := rfl

/-- Every class in the honest image has a relative representative. -/
theorem perfectSupportedOpenKZeroToImage_surjective : Function.Surjective
  (perfectSupportedOpenKZeroToImage j T) := by
  rintro ⟨x, a, rfl⟩
  refine ⟨perfectSupportedOpenKMap j T 0 a, ?_⟩
  apply Subtype.ext
  exact DFunLike.congr_fun (perfectSupportedOpenKRestrict_comp_perfectSupportedOpenKMap j T 0) a

/-- Its kernel is exactly the kernel of the original relative restriction. -/
@[simp] theorem perfectSupportedOpenKZeroToImage_ker :
    (perfectSupportedOpenKZeroToImage j T).ker = (perfectSupportedOpenKRestrict j T 0).ker := by
  ext a
  change (perfectSupportedOpenKZeroToImage j T a = 1) ↔ perfectSupportedOpenKRestrict j T 0 a = 1
  exact Subtype.ext_iff

/-- The always-valid image theorem is a quotient by the actual remaining kernel.
Identifying the relative endpoint itself with this image still requires injectivity. -/
def perfectSupportedOpenKZeroQuotientImageEquiv :
    PerfectSupportedOpenCoarseK j T 0 ⧸ (perfectSupportedOpenKZeroToImage j T).ker ≃*
      PerfectSupportedOpenKZeroImage j T :=
  QuotientGroup.quotientKerEquivOfSurjective (perfectSupportedOpenKZeroToImage j T)
    (perfectSupportedOpenKZeroToImage_surjective j T)

/-- The image equivalence sends each original relative class to its original restriction. -/
@[simp] theorem perfectSupportedOpenKZeroQuotientImageEquiv_mk
    (a : PerfectSupportedOpenCoarseK j T 0) :
    (perfectSupportedOpenKZeroQuotientImageEquiv j T (QuotientGroup.mk a) : PerfectSupportedK (j ⁻¹ᵁ
      T).ι 0) =
      perfectSupportedOpenKRestrict j T 0 a := rfl

/-- A surjectivity claim onto all target K-zero is exactly the corresponding
claim for original restriction; the relative factor does not supply it. -/
theorem perfectSupportedOpenKRestrict_zero_surjective_iff :
    Function.Surjective (perfectSupportedOpenKRestrict j T 0) ↔ Function.Surjective
      (perfectSupportedKRestrict j T 0) := by
  constructor
  · intro hs y
    obtain ⟨a, ha⟩ := hs y
    obtain ⟨b, hb⟩ := perfectSupportedOpenKMap_zero_surjective j T a
    refine ⟨b, ?_⟩
    rw [← DFunLike.congr_fun (perfectSupportedOpenKRestrict_comp_perfectSupportedOpenKMap j T 0) b,
      MonoidHom.comp_apply, hb, ha]
  · intro hs y
    obtain ⟨a, rfl⟩ := hs y
    exact ⟨perfectSupportedOpenKMap j T 0 a, DFunLike.congr_fun
      (perfectSupportedOpenKRestrict_comp_perfectSupportedOpenKMap j T 0) a⟩

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0334",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/KZeroImage.lean:32-110"
    "adaptation"
    "Actual supported coarse restriction range and quotient-image theorem; no injectivity assumed"]
  AlgebraicGeometry.Scheme.Modules.range_perfectSupportedOpenKRestrict_zero
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpenKZeroToImage
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpenKZeroToImage_surjective
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpenKZeroQuotientImageEquiv
