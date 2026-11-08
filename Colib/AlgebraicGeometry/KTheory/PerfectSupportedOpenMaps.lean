/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenSupport
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenSupport

/-!
# Canonical K-maps with prescribed support

The relative coarse group is distinguished from the fine supported group on the
open. Literal restriction factors through change of weak equivalences. Flattening
preserves the actual support-union inclusion in every connective degree.
Adapted from Quillen SupportedOpen/{Restriction,Fibration,Support}.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Waldhausen Fibration
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The K-map induced by literal exact supported restriction. -/
def perfectSupportedKRestrict (n : ℕ) :
    PerfectSupportedK T.ι n →* PerfectSupportedK (j ⁻¹ᵁ T).ι n :=
  KMap (perfectSupportedRestrict_exact j T) n

/-- Forgetting support commutes with the actual restriction K-map. -/
theorem perfectSupportedKRestrict_comp_forget (n : ℕ) :
    (perfectSupportedKMap (j ⁻¹ᵁ T).ι n).comp (perfectSupportedKRestrict j T n) =
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) n).comp
        (perfectSupportedKMap T.ι n) := by
  unfold perfectSupportedKMap perfectSupportedKRestrict
  rw [KMap_comp_KMap, KMap_comp_KMap]

/-- Connective K-theory of the named relative-open coarse model. -/
abbrev PerfectSupportedOpenCoarseK (n : ℕ) := (perfectSupportedOpenWeakWaldhausen j T).K n

/-- The original change-of-weak-equivalences map, on the unchanged perfect category. -/
def perfectSupportedOpenKMap (n : ℕ) :
    PerfectSupportedK T.ι n →* PerfectSupportedOpenCoarseK j T n :=
  Waldhausen.KMap (Waldhausen.Fibration.changeWeak_exact (perfectSupportedOpenNested j T)) n

/-- Restriction from the relative coarse model to actual perfect complexes on the open. -/
def perfectSupportedOpenKRestrict (n : ℕ) :
    PerfectSupportedOpenCoarseK j T n →* PerfectSupportedK (j ⁻¹ᵁ T).ι n :=
  Waldhausen.KMap (perfectSupportedOpenRestrict_waldhausenExact j T) n

/-- The original open-restriction K-map factors through the named coarse model. -/
theorem perfectSupportedOpenKRestrict_comp_perfectSupportedOpenKMap (n : ℕ) :
    (perfectSupportedOpenKRestrict j T n).comp (perfectSupportedOpenKMap j T n) =
      perfectSupportedKRestrict j T n := by
  unfold perfectSupportedOpenKRestrict perfectSupportedOpenKMap perfectSupportedKRestrict
  rw [Waldhausen.KMap_comp_KMap]

/-- Forget only the additional acyclicity on the open, retaining the prescribed support. -/
def perfectSupportedUnionKMap (n : ℕ) :
    PerfectSupportedK (T ⊔ j.opensRange).ι n →* PerfectSupportedK T.ι n :=
  KMap ((perfectSupportedUnionToAcyclic_exact j T).comp
    (acyclicInclusion_exact (perfectSupportedOpenNested j T))) n

/-- The genuine all-degree K-equivalence of the two original supported models. -/
def perfectSupportedOpenAcyclicSupportedKEquiv (n : ℕ) :
    (acyclicStructure (perfectSupportedOpenNested j T)).K n ≃* PerfectSupportedK (T ⊔
      j.opensRange).ι n :=
  KEquivOfExactEquivalence (perfectSupportedOpenAcyclicSupportedEquivalence j T)
    (perfectSupportedOpenAcyclicToSupported_exact j T) (perfectSupportedUnionToAcyclic_exact j T) n

/-- The forward equivalence is the actual K-map of literal flattening. -/
theorem perfectSupportedOpenAcyclicSupportedKEquiv_toMonoidHom (n : ℕ) :
    (perfectSupportedOpenAcyclicSupportedKEquiv j T n).toMonoidHom =
      KMap (perfectSupportedOpenAcyclicToSupported_exact j T) n := rfl

/-- Flattening intertwines the original supported inclusion, literally its public K-map. -/
theorem perfectSupportedOpenAcyclicSupportedKEquiv_inclusion (n : ℕ) :
    (perfectSupportedUnionKMap j T n).comp (perfectSupportedOpenAcyclicSupportedKEquiv j T
      n).toMonoidHom =
      KMap (acyclicInclusion_exact (perfectSupportedOpenNested j T)) n := by
  change (KMap ((perfectSupportedUnionToAcyclic_exact j T).comp
    (acyclicInclusion_exact (perfectSupportedOpenNested j T))) n).comp
      (KMap (perfectSupportedOpenAcyclicToSupported_exact j T) n) = _
  rw [KMap_comp_KMap]

/-- The inverse K-equivalence identifies the same canonical supported inclusion. -/
theorem perfectSupportedOpenAcyclicSupportedKEquiv_symm_inclusion (n : ℕ) :
    (KMap (acyclicInclusion_exact (perfectSupportedOpenNested j T)) n).comp
      (perfectSupportedOpenAcyclicSupportedKEquiv j T n).symm.toMonoidHom =
        perfectSupportedUnionKMap j T n := by
  ext x
  have h := DFunLike.congr_fun (perfectSupportedOpenAcyclicSupportedKEquiv_inclusion j T n)
    ((perfectSupportedOpenAcyclicSupportedKEquiv j T n).symm x)
  simpa using h.symm

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0331",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Support.lean:184-218"
    "adaptation"
    "Native supported relative-open coarse model and actual maps, without fine-open comparison"]
  AlgebraicGeometry.Scheme.Modules.perfectSupportedUnionKMap
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpenAcyclicSupportedKEquiv
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpenAcyclicSupportedKEquiv_inclusion
