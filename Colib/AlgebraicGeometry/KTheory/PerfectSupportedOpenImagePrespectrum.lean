/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenPrespectrumMaps
public import Colib.AlgebraicGeometry.KTheory.SupportedOpenQcqsComparison

/-!
# The actual supported coarse connective image cover

The original coarse S-prespectrum has precisely the restriction image in stable degree
zero. Under qcqs ambient and compact union hypotheses, actual supported restriction is
bijective in positive degrees and injective in degree zero. No compactness of U alone,
abstract cover-spectrum data or supplied roof/complement hypothesis is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology Topology.LoopPrespectrum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- Degree-zero stable restriction has exactly the actual global fine restriction image. -/
theorem perfectSupportedOpenRestrictPrespectrumMap_zero_mem_range_iff
    (b : (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).K 0) :
    (∃ a : stableHomotopyGroup (perfectSupportedOpenPrespectrum j T) 0,
      (stableHomotopyFunctor 0).map (perfectSupportedOpenRestrictPrespectrumMap j T) a =
        originalKStableEquiv (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) 0
          (Additive.ofMul b)) ↔ b ∈ PerfectSupportedOpenKZeroImage j T := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨x, rfl⟩ := (originalKStableEquiv (perfectSupportedOpenWeakWaldhausen j T)
      0).surjective a
    have hx : perfectSupportedOpenKRestrict j T 0 x.toMul = b :=
      (originalKStableEquiv (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) 0).injective
        ((perfectSupportedOpenRestrictPrespectrumMap_naturality j T 0 x.toMul).trans ha)
    change b ∈ (perfectSupportedKRestrict j T 0).range
    rw [← range_perfectSupportedOpenKRestrict_zero j T]
    exact ⟨x.toMul, hx⟩
  · intro hb
    change b ∈ (perfectSupportedKRestrict j T 0).range at hb
    rw [← range_perfectSupportedOpenKRestrict_zero j T] at hb
    obtain ⟨x, rfl⟩ := hb
    exact ⟨originalKStableEquiv (perfectSupportedOpenWeakWaldhausen j T) 0 (Additive.ofMul x),
      (perfectSupportedOpenRestrictPrespectrumMap_naturality j T 0 x).symm⟩

variable [CompactSpace X] [QuasiSeparatedSpace X]
  (hW : IsCompact ((j.opensRange ⊔ T : X.Opens) : Set X))

include hW in
/-- Positive stable restriction is bijective, using only native roofs and perfect complements. -/
theorem perfectSupportedOpenRestrictPrespectrumMap_succ_bijective_of_union_compact (n : ℕ) :
    Function.Bijective ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
      (perfectSupportedOpenRestrictPrespectrumMap j T)) :=
  (exactStableKMap_nonnegative_bijective_iff (perfectSupportedOpenWeakWaldhausen j T)
    (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι)
    (perfectSupportedOpenRestrict_waldhausenExact j T) (n + 1)).mpr
      (perfectSupportedOpenKRestrict_succ_bijective_of_union_compact j T hW n)

/-- The actual relative stable degree-zero group identifies with the exact restriction image. -/
def perfectSupportedOpenStableZeroImageEquivOfUnionCompact :
    stableHomotopyGroup (perfectSupportedOpenPrespectrum j T) 0 ≃+ Additive
      (PerfectSupportedOpenKZeroImage j T) :=
  (originalKStableEquiv (perfectSupportedOpenWeakWaldhausen j T) 0).symm.trans
    (perfectSupportedOpenKZeroImageEquivOfUnionCompact j T hW).toAdditive

/-- Forgetting image membership recovers the original stable restriction, not another map. -/
theorem perfectSupportedOpenStableZeroImageEquivOfUnionCompact_coe
    (a : stableHomotopyGroup (perfectSupportedOpenPrespectrum j T) 0) :
    originalKStableEquiv (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) 0
        (Additive.ofMul ((perfectSupportedOpenStableZeroImageEquivOfUnionCompact j T hW a).toMul :
          (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).K 0)) =
      (stableHomotopyFunctor 0).map (perfectSupportedOpenRestrictPrespectrumMap j T) a := by
  have h := perfectSupportedOpenRestrictPrespectrumMap_naturality j T 0
    ((originalKStableEquiv (perfectSupportedOpenWeakWaldhausen j T) 0).symm a).toMul
  exact h.trans (congrArg
    (fun b => (stableHomotopyFunctor 0).map (perfectSupportedOpenRestrictPrespectrumMap j T) b)
    ((originalKStableEquiv (perfectSupportedOpenWeakWaldhausen j T) 0).apply_symm_apply a))

include hW in
/-- Degree-zero stable restriction is injective, without asserting surjectivity onto all K-zero. -/
theorem perfectSupportedOpenRestrictPrespectrumMap_zero_injective_of_union_compact :
    Function.Injective ((stableHomotopyFunctor 0).map (perfectSupportedOpenRestrictPrespectrumMap
      j T)) := by
  intro a b hab
  apply (perfectSupportedOpenStableZeroImageEquivOfUnionCompact j T hW).injective
  have h := (perfectSupportedOpenStableZeroImageEquivOfUnionCompact_coe j T hW a).trans
    (hab.trans (perfectSupportedOpenStableZeroImageEquivOfUnionCompact_coe j T hW b).symm)
  have hv := (originalKStableEquiv
    (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) 0).injective h
  exact Subtype.ext hv

attribute [colib_tag "COL-0335"]
  perfectSupportedOpenRestrictPrespectrumMap_zero_mem_range_iff
  perfectSupportedOpenRestrictPrespectrumMap_succ_bijective_of_union_compact
  perfectSupportedOpenStableZeroImageEquivOfUnionCompact
  perfectSupportedOpenStableZeroImageEquivOfUnionCompact_coe
  perfectSupportedOpenRestrictPrespectrumMap_zero_injective_of_union_compact

end AlgebraicGeometry.Scheme.Modules
