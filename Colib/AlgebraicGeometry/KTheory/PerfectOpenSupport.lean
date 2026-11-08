/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectOpenSupport
public import Colib.AlgebraicGeometry.KTheory.PerfectRestriction
public import Colib.KTheory.Waldhausen.ExactEquivalence

/-! # Canonical K-maps for native open support

Adapted from Quillen OpenFibration:119-139 and OpenSupport:191-218 at
c561118b7795eb9780be9ed391c3251d6a4d0afd. These are the actual canonical maps,
with the existing zero rebasing. No fine-open localization equivalence is claimed.
-/
@[expose] public noncomputable section
open CategoryTheory Waldhausen Fibration
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

/-- K-theory of the relative coarse model. -/
abbrev PerfectOpenK (n : ℕ) := (perfectOpenWeakWaldhausen j).K n

/-- Change only the weak class on the original native perfect category. -/
def perfectOpenKMap (n : ℕ) :
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K n →* PerfectOpenK j n :=
  KMap (changeWeak_exact (perfectOpenNested j)) n

/-- The canonical restriction map from the coarse model. -/
def perfectOpenKRestrict (n : ℕ) : PerfectOpenK j n →*
    (RingedSpace.perfectComplexesWaldhausen Y.toRingedSpace).K n :=
  KMap (perfectOpenRestrict_isExact j) n

/-- The existing native restriction K-map factors through the relative coarse model. -/
@[colib_tag "COL-0298"]
theorem perfectOpenKRestrict_comp_perfectOpenKMap (n : ℕ) :
    (perfectOpenKRestrict j n).comp (perfectOpenKMap j n) =
      KMap (perfectComplexesRestrictOpenImmersion_isExact j) n := by
  exact KMap_comp_KMap (changeWeak_exact (perfectOpenNested j))
    (perfectOpenRestrict_isExact j) n

/-- Fine K-theory of the actual supported category. -/
abbrev PerfectSupportedK (n : ℕ) := (perfectSupportedWaldhausen j).K n

/-- The actual supported inclusion's canonical K-map. -/
def perfectSupportedKMap (n : ℕ) : PerfectSupportedK j n →*
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K n :=
  KMap (perfectSupportedInclusion_isExact j) n

/-- Exact flattening gives the actual all-degree K-equivalence. -/
@[colib_tag "COL-0298"]
def perfectAcyclicSupportedKEquiv (n : ℕ) :
    (acyclicStructure (perfectOpenNested j)).K n ≃* PerfectSupportedK j n :=
  KEquivOfExactEquivalence (perfectAcyclicSupportedEquivalence j)
    (perfectAcyclicToSupported_exact j) (perfectSupportedToAcyclic_exact j) n

/-- Flattening intertwines the original canonical supported inclusion. -/
@[colib_tag "COL-0298"]
theorem perfectAcyclicSupportedKEquiv_inclusion (n : ℕ) :
    (perfectSupportedKMap j n).comp
      (perfectAcyclicSupportedKEquiv j n).toMonoidHom =
      KMap (acyclicInclusion_exact (perfectOpenNested j)) n := by
  exact KMap_comp_KMap (perfectAcyclicToSupported_exact j)
    (perfectSupportedInclusion_isExact j) n

/-- The inverse identifies the same canonical inclusion. -/
theorem perfectAcyclicSupportedKEquiv_symm_inclusion (n : ℕ) :
    (KMap (acyclicInclusion_exact (perfectOpenNested j)) n).comp
      (perfectAcyclicSupportedKEquiv j n).symm.toMonoidHom =
      perfectSupportedKMap j n := by
  ext x
  have h := DFunLike.congr_fun (perfectAcyclicSupportedKEquiv_inclusion j n)
    ((perfectAcyclicSupportedKEquiv j n).symm x)
  simpa using h.symm

/-- On a literal open subset, the general restriction is the original native functor.
Only the proof of native perfectness changes; proof irrelevance identifies the lifts. -/
@[simp] theorem perfectComplexesRestrictOpenImmersion_opens (X : Scheme.{u}) (U : X.Opens) :
    perfectComplexesRestrictOpenImmersion U.ι = perfectComplexesRestrictFunctor X U := rfl

/-- The original public opens-only restriction K-map factors through the same general model. -/
theorem perfectOpenKRestrict_comp_perfectOpenKMap_opens (X : Scheme.{u}) (U : X.Opens)
    (n : ℕ) :
    (perfectOpenKRestrict U.ι n).comp (perfectOpenKMap U.ι n) =
      perfectComplexesRestrictKMap X U n := by
  rw [perfectOpenKRestrict_comp_perfectOpenKMap]
  change KMap (perfectComplexesRestrictOpenImmersion_isExact U.ι) n =
    KMap (perfectComplexesRestrictFunctor_isExact X U) n
  rfl

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/OpenSupport.lean:180-200" "adaptation"
  "Exact acyclic/support flattening with native ambient-monomorphism cofibrations"]
  AlgebraicGeometry.Scheme.Modules.perfectAcyclicSupportedKEquiv
