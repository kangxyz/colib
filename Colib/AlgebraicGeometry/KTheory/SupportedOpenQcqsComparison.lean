/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.SupportedOpenDerivedImage.QcqsGeometry
public import Colib.AlgebraicGeometry.KTheory.SupportedOpenDerivedImageCofinality

/-!
# Supported qcqs comparison on the actual restriction maps

The union-compact geometric proofs discharge every roof and complement premise.
The coarse-to-fine map is bijective in positive degrees and injective in degree zero.
Its degree-zero image is exactly the image of the actual fine global restriction.
These statements do not assert surjectivity onto the whole local K-zero group or
coherent transport of a prespectrum fiber.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  [CompactSpace X] [QuasiSeparatedSpace X]
  (hW : IsCompact ((j.opensRange ⊔ T : X.Opens) : Set X))

open SupportedOpenDerivedImage

include hW in
/-- Actual supported restriction is bijective in positive degrees. -/
theorem perfectSupportedOpenKRestrict_succ_bijective_of_union_compact (n : ℕ) :
    Function.Bijective (perfectSupportedOpenKRestrict j T (n + 1)) := by
  let : Fact (HasDerivedRoofs j T) := ⟨hasDerivedRoofs_of_union_compact j T hW⟩
  exact relativeKRestrict_succ_bijective j T (hasPerfectComplements_of_union_compact j T hW) n

include hW in
/-- Actual supported restriction remains injective in degree zero. -/
theorem perfectSupportedOpenKRestrict_injective_of_union_compact (n : ℕ) :
    Function.Injective (perfectSupportedOpenKRestrict j T n) := by
  let : Fact (HasDerivedRoofs j T) := ⟨hasDerivedRoofs_of_union_compact j T hW⟩
  exact relativeKRestrict_injective j T (hasPerfectComplements_of_union_compact j T hW) n

/-- The forward positive equivalence is the original supported restriction. -/
def perfectSupportedOpenKEquivOfUnionCompact (n : ℕ) :
    PerfectSupportedOpenCoarseK j T (n + 1) ≃* PerfectSupportedK (j ⁻¹ᵁ T).ι (n + 1) :=
  MulEquiv.ofBijective (perfectSupportedOpenKRestrict j T (n + 1))
    (perfectSupportedOpenKRestrict_succ_bijective_of_union_compact j T hW n)

@[simp] theorem perfectSupportedOpenKEquivOfUnionCompact_apply (n : ℕ)
    (x : PerfectSupportedOpenCoarseK j T (n + 1)) :
    perfectSupportedOpenKEquivOfUnionCompact j T hW n x =
      perfectSupportedOpenKRestrict j T (n + 1) x := rfl

/-- Coarse degree zero is exactly the actual fine restriction-image subgroup. -/
def perfectSupportedOpenKZeroImageEquivOfUnionCompact :
    PerfectSupportedOpenCoarseK j T 0 ≃* PerfectSupportedOpenKZeroImage j T :=
  MulEquiv.ofBijective (perfectSupportedOpenKZeroToImage j T)
    ⟨fun _ _ h => perfectSupportedOpenKRestrict_injective_of_union_compact j T hW 0
      (congrArg Subtype.val h), perfectSupportedOpenKZeroToImage_surjective j T⟩

@[simp] theorem perfectSupportedOpenKZeroImageEquivOfUnionCompact_coe
    (x : PerfectSupportedOpenCoarseK j T 0) :
    (perfectSupportedOpenKZeroImageEquivOfUnionCompact j T hW x :
      PerfectSupportedK (j ⁻¹ᵁ T).ι 0) = perfectSupportedOpenKRestrict j T 0 x := rfl

/-- Compact source and compact auxiliary open imply the positive comparison. -/
theorem perfectSupportedOpenKRestrict_succ_bijective_of_qcqs [CompactSpace U]
    (hT : IsCompact (T : Set X)) (n : ℕ) :
    Function.Bijective (perfectSupportedOpenKRestrict j T (n + 1)) :=
  perfectSupportedOpenKRestrict_succ_bijective_of_union_compact j T
    (isCompact_supportedUnion j T hT) n

/-- The same compact-open hypotheses preserve injectivity in all connective degrees. -/
theorem perfectSupportedOpenKRestrict_injective_of_qcqs [CompactSpace U]
    (hT : IsCompact (T : Set X)) (n : ℕ) :
    Function.Injective (perfectSupportedOpenKRestrict j T n) :=
  perfectSupportedOpenKRestrict_injective_of_union_compact j T
    (isCompact_supportedUnion j T hT) n

end AlgebraicGeometry.Scheme.Modules
