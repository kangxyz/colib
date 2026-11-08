/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.OpenDerivedImageCofinality

/-!
# Conditional connective localization for native perfect complexes

Actual native derived roofs and perfect complements identify the relative-open K-groups
with fine perfect K-theory in positive degrees. Transporting the existing boundary through
this proved equivalence gives all three exact positions and the honest degree-zero tail.
The relative zero endpoint is the actual global restriction image, not all open K-zero.

The two geometric existence inputs remain explicit. This is the group-level connective
localization endpoint, not the full TT spectrum comparison or Bass nonconnective localization.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/GlobalLocalization.lean:39-153`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The unconditional qcqs geometry in that
implementation is replaced by the precise native roof and complement inputs of COL-0315.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
namespace AlgebraicGeometry.Scheme.Modules

universe u d

open OpenDerivedImage

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Fine global restriction with codomain restricted to its actual degree-zero image. -/
def perfectKZeroToOpenImage :
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K 0 →*
      PerfectOpenKZeroImage j :=
  (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0).codRestrict
    (PerfectOpenKZeroImage j) (fun a => ⟨a, rfl⟩)

/-- The image endpoint forgets membership to the unchanged fine restriction map. -/
@[simp] theorem perfectKZeroToOpenImage_coe
    (a : (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K 0) :
    (perfectKZeroToOpenImage j a :
      (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K 0) =
        KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0 a := rfl

/-- The honest image endpoint is surjective without any geometric existence assumption. -/
theorem perfectKZeroToOpenImage_surjective : Function.Surjective (perfectKZeroToOpenImage j) := by
  rintro ⟨x, a, rfl⟩
  exact ⟨a, rfl⟩

/-- Restricting the codomain to the honest image leaves the actual kernel unchanged. -/
@[simp] theorem perfectKZeroToOpenImage_ker :
    (perfectKZeroToOpenImage j).ker =
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0).ker := by
  ext a
  change (perfectKZeroToOpenImage j a = 1) ↔
    KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0 a = 1
  exact Subtype.ext_iff


variable [HasDerivedCategory.{d} U.Modules] [Fact (HasDerivedRoofs j)]
  (hc : HasPerfectComplements j)

/-- Genuine supported boundary from native fine perfect K-theory of the open. -/
def perfectOpenFineConnectingHom (n : ℕ) :
    (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K (n + 1) →*
      PerfectSupportedK j n :=
  (perfectOpenConnectingHom j n).comp
    (relativeKRestrictEquiv j hc n).symm.toMonoidHom

/-- The transported boundary retains the entire original relative boundary homomorphism. -/
theorem perfectOpenFineConnectingHom_comp_relative (n : ℕ) :
    (perfectOpenFineConnectingHom j hc n).comp
      (perfectOpenKRestrict j (n + 1)) =
    perfectOpenConnectingHom j n := by
  ext a
  change perfectOpenConnectingHom j n
    ((relativeKRestrictEquiv j hc n).symm ((relativeKRestrictEquiv j hc n) a)) = _
  rw [MulEquiv.symm_apply_apply]

include hc in
/-- Exactness at native fine perfect K-theory on the base, including degree zero. -/
theorem range_perfectSupportedKMap_eq_ker_perfectRestrictKMap (n : ℕ) :
    (perfectSupportedKMap j n).range =
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) n).ker := by
  rw [range_perfectSupportedKMap_eq_ker_perfectOpenKMap]
  ext x
  change perfectOpenKMap j n x = 1 ↔
    KMap (perfectComplexesRestrictOpenImmersion_isExact j) n x = 1
  have he := DFunLike.congr_fun
    (perfectOpenKRestrict_comp_perfectOpenKMap j n) x
  constructor
  · intro hx
    rw [← he, MonoidHom.comp_apply, hx, map_one]
  · intro hx
    apply relativeKRestrict_injective j hc n
    exact he.trans (hx.trans (map_one _).symm)

/-- The new boundary has exactly the original relative boundary image. -/
theorem range_perfectOpenFineConnectingHom (n : ℕ) :
    (perfectOpenFineConnectingHom j hc n).range =
      (perfectOpenConnectingHom j n).range := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(relativeKRestrictEquiv j hc n).symm a, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨relativeKRestrictEquiv j hc n a, ?_⟩
    exact DFunLike.congr_fun (perfectOpenFineConnectingHom_comp_relative j hc n) a

/-- Exactness at original supported perfect K-theory, including its degree-zero group. -/
theorem range_perfectOpenFineConnectingHom_eq_ker_perfectSupportedKMap (n : ℕ) :
    (perfectOpenFineConnectingHom j hc n).range =
      (perfectSupportedKMap j n).ker := by
  rw [range_perfectOpenFineConnectingHom,
    range_perfectOpenConnectingHom_eq_ker_perfectSupportedKMap]

/-- Exactness at positive native fine perfect K-theory of the open. -/
theorem range_perfectRestrictKMap_eq_ker_perfectOpenFineConnectingHom (n : ℕ) :
    (KMap (perfectComplexesRestrictOpenImmersion_isExact j) (n + 1)).range =
      (perfectOpenFineConnectingHom j hc n).ker := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change perfectOpenFineConnectingHom j hc n
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) (n + 1) a) = 1
    rw [← DFunLike.congr_fun
      (perfectOpenKRestrict_comp_perfectOpenKMap j (n + 1)) a]
    change ((perfectOpenFineConnectingHom j hc n).comp
      (perfectOpenKRestrict j (n + 1)))
      (perfectOpenKMap j (n + 1) a) = 1
    rw [perfectOpenFineConnectingHom_comp_relative]
    have hm : perfectOpenKMap j (n + 1) a ∈
        (perfectOpenKMap j (n + 1)).range := ⟨a, rfl⟩
    rw [range_perfectOpenKMap_eq_ker_perfectOpenConnectingHom] at hm
    exact hm
  · intro hx
    have hm : (relativeKRestrictEquiv j hc n).symm x ∈
        (perfectOpenConnectingHom j n).ker := hx
    rw [← range_perfectOpenKMap_eq_ker_perfectOpenConnectingHom] at hm
    obtain ⟨a, ha⟩ := hm
    refine ⟨a, ?_⟩
    rw [← DFunLike.congr_fun
      (perfectOpenKRestrict_comp_perfectOpenKMap j (n + 1)) a]
    change relativeKRestrictEquiv j hc n
      (perfectOpenKMap j (n + 1) a) = x
    rw [ha, MulEquiv.apply_symm_apply]

/-- All recurring positions of the conditional fine-open connective localization sequence. -/
theorem perfectOpenFine_positiveLongExactSequence (n : ℕ) :
    (KMap (perfectComplexesRestrictOpenImmersion_isExact j) (n + 1)).range =
      (perfectOpenFineConnectingHom j hc n).ker ∧
    (perfectOpenFineConnectingHom j hc n).range =
      (perfectSupportedKMap j n).ker ∧
    (perfectSupportedKMap j n).range =
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) n).ker :=
  ⟨range_perfectRestrictKMap_eq_ker_perfectOpenFineConnectingHom j hc n,
    range_perfectOpenFineConnectingHom_eq_ker_perfectSupportedKMap j hc n,
    range_perfectSupportedKMap_eq_ker_perfectRestrictKMap j hc n⟩

/-- The actual K₁(open) → K₀(support) → K₀(base) → K₀(open) exact tail. -/
theorem perfectOpenFine_zeroTail :
    (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 1).range =
      (perfectOpenFineConnectingHom j hc 0).ker ∧
    (perfectOpenFineConnectingHom j hc 0).range =
      (perfectSupportedKMap j 0).ker ∧
    (perfectSupportedKMap j 0).range =
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0).ker :=
  perfectOpenFine_positiveLongExactSequence j hc 0

/-- Compatibility with the unchanged relative boundary determines this endpoint uniquely. -/
theorem perfectOpenFineConnectingHom_unique (n : ℕ)
    (δ : (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K (n + 1) →*
      PerfectSupportedK j n)
    (hδ : δ.comp (perfectOpenKRestrict j (n + 1)) = perfectOpenConnectingHom j n) :
    δ = perfectOpenFineConnectingHom j hc n := by
  ext x
  obtain ⟨a, rfl⟩ := (relativeKRestrictEquiv j hc n).surjective x
  exact DFunLike.congr_fun (hδ.trans (perfectOpenFineConnectingHom_comp_relative j hc n).symm) a

/-- The canonical relative-zero equivalence intertwines the actual change-of-weakness map. -/
theorem relativeKZeroImageEquiv_comp_perfectOpenKMap :
    (relativeKZeroImageEquiv j hc).toMonoidHom.comp (perfectOpenKMap j 0) =
      perfectKZeroToOpenImage j := by
  ext a
  exact DFunLike.congr_fun (perfectOpenKRestrict_comp_perfectOpenKMap j 0) a

/-- The terminal zero in the connective tail is valid for the actual image subgroup only. -/
theorem perfectOpenFine_zeroImageTail :
    (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 1).range =
      (perfectOpenFineConnectingHom j hc 0).ker ∧
    (perfectOpenFineConnectingHom j hc 0).range = (perfectSupportedKMap j 0).ker ∧
    (perfectSupportedKMap j 0).range = (perfectKZeroToOpenImage j).ker ∧
    Function.Surjective (perfectKZeroToOpenImage j) := by
  rw [perfectKZeroToOpenImage_ker]
  exact ⟨(perfectOpenFine_zeroTail j hc).1, (perfectOpenFine_zeroTail j hc).2.1,
    (perfectOpenFine_zeroTail j hc).2.2, perfectKZeroToOpenImage_surjective j⟩

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0318",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/GlobalLocalization.lean:39-153"
    "adaptation"
    "Fine boundary, three exact positions and uniqueness with native roof/complement inputs"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenFineConnectingHom
  AlgebraicGeometry.Scheme.Modules.perfectOpenFineConnectingHom_comp_relative
  AlgebraicGeometry.Scheme.Modules.perfectOpenFine_positiveLongExactSequence
  AlgebraicGeometry.Scheme.Modules.perfectOpenFine_zeroTail
  AlgebraicGeometry.Scheme.Modules.perfectOpenFineConnectingHom_unique

attribute [colib_tag "COL-0318",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/OpenKZeroImage.lean:38-65"
    "adaptation" "Actual fine restriction image as the surjective degree-zero endpoint"]
  AlgebraicGeometry.Scheme.Modules.perfectKZeroToOpenImage
  AlgebraicGeometry.Scheme.Modules.relativeKZeroImageEquiv_comp_perfectOpenKMap
  AlgebraicGeometry.Scheme.Modules.perfectOpenFine_zeroImageTail

attribute [colib_ref "ThomasonTrobaugh1990" "Section 5.1, pp. 337-338" "adaptation"
  "Conditional connective group endpoint with actual K-zero image; not the full spectrum theorem"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenFine_positiveLongExactSequence
  AlgebraicGeometry.Scheme.Modules.perfectOpenFine_zeroImageTail
