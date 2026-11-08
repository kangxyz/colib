/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectOpenImageCoverDiagram
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenConnectiveLocalization
public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.QcqsGeometry

/-!
# Fixed-pair qcqs connective image-cover localization

For a quasi-compact open in a quasi-compact quasi-separated scheme, the actual coarse
prespectrum is the image-cover target of Thomason--Trobaugh 5.1.1. Geometric roofs and
complements are proved by the native qcqs geometry, not supplied as hypotheses.
The existing restriction, supported inclusion, nullhomotopy and fiber lift are retained.
The support means perfect complexes on X acyclic on U, not perfect complexes on X minus U.

The fixed-pair conclusion does not assert TT 5.1.2 with an additional closed support,
arbitrary open-pair pullback naturality, or the nonconnective Bass theorem of TT 7.4.
The proof follows TT 5.2, pp. 337--338, using the actual coarse-to-fine map.
Implementation provenance: Quillen PerfectComplexes/GlobalLocalization.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd, with native Mathlib/Stacks geometry.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology Topology.LoopPrespectrum

namespace AlgebraicGeometry.Scheme.Modules

universe u d

variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j] [HasDerivedCategory.{d} U.Modules]

/-- Positive stable restriction is bijective for the actual coarse target under qcqs
hypotheses only. The derived category model of the open may be chosen arbitrarily. -/
theorem perfectOpenRestrictPrespectrumMap_succ_bijective_of_qcqs (n : ℕ) :
    Function.Bijective ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
      (perfectOpenRestrictPrespectrumMap j)) := by
  let : Fact (OpenDerivedImage.HasDerivedRoofs j) :=
    ⟨OpenDerivedImage.hasDerivedRoofs_of_qcqs j⟩
  exact perfectOpenRestrictPrespectrumMap_succ_bijective j
    (OpenDerivedImage.hasPerfectComplements_of_qcqs j) n

/-- Stable degree zero of the actual target is precisely the restriction image. -/
def perfectOpenStableZeroImageEquivOfQcqs :
    stableHomotopyGroup (perfectOpenPrespectrum j) 0 ≃+ Additive (PerfectOpenKZeroImage j) := by
  letI : Fact (OpenDerivedImage.HasDerivedRoofs j) :=
    ⟨OpenDerivedImage.hasDerivedRoofs_of_qcqs j⟩
  exact perfectOpenStableZeroImageEquiv j (OpenDerivedImage.hasPerfectComplements_of_qcqs j)

/-- The qcqs image equivalence forgets to the actual restriction, with no change of map. -/
theorem perfectOpenStableZeroImageEquivOfQcqs_coe
    (a : stableHomotopyGroup (perfectOpenPrespectrum j) 0) :
    originalKStableEquiv (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace) 0
        (Additive.ofMul ((perfectOpenStableZeroImageEquivOfQcqs j a).toMul :
          (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K 0)) =
      (stableHomotopyFunctor 0).map (perfectOpenRestrictPrespectrumMap j) a := by
  let : Fact (OpenDerivedImage.HasDerivedRoofs j) :=
    ⟨OpenDerivedImage.hasDerivedRoofs_of_qcqs j⟩
  exact perfectOpenStableZeroImageEquiv_coe j
    (OpenDerivedImage.hasPerfectComplements_of_qcqs j) a

/-- Degree zero is injective, and is not asserted surjective onto all K-zero of the open. -/
theorem perfectOpenRestrictPrespectrumMap_zero_injective_of_qcqs :
    Function.Injective ((stableHomotopyFunctor 0).map
      (perfectOpenRestrictPrespectrumMap j)) := by
  let : Fact (OpenDerivedImage.HasDerivedRoofs j) :=
    ⟨OpenDerivedImage.hasDerivedRoofs_of_qcqs j⟩
  exact perfectOpenRestrictPrespectrumMap_zero_injective j
    (OpenDerivedImage.hasPerfectComplements_of_qcqs j)

/-- Fixed-pair TT 5.1.1, with the actual coarse target and the actual supported fiber lift.
This collects proved constructions, rather than assuming an image-cover profile. The exact
zero image is identified by `perfectOpenStableZeroImageEquivOfQcqs_coe` and the existing
`perfectOpenRestrictPrespectrumMap_zero_mem_range_iff`. The lift's entire path and structure
square are `perfectSupportedFiberPrespectrumMap_path` and
`perfectSupportedPrespectrumNullhomotopy_structure`. -/
@[colib_tag "COL-0330",
  colib_ref "ThomasonTrobaugh1990" "Theorem 5.1.1 and proof 5.2, pp. 337-338" "adaptation"
    "Fixed qcqs open pair, actual connective coarse image-cover and supported fiber map"]
theorem perfectQcqs_connectiveImageCoverLocalization :
    IsOmega (perfectOpenPrespectrum j) ∧
    (∀ k : ℤ, k < 0 → Subsingleton (stableHomotopyGroup (perfectOpenPrespectrum j) k)) ∧
    (∀ n : ℕ, Function.Bijective ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
      (perfectOpenRestrictPrespectrumMap j))) ∧
    Function.Injective ((stableHomotopyFunctor 0).map (perfectOpenRestrictPrespectrumMap j)) ∧
    Nonempty (Homotopy
      (Fibration.changeWeakPrespectrumMap (perfectOpenNested j) ≫
        perfectOpenRestrictPrespectrumMap j) (perfectFlatPrespectrumMap j)) ∧
    perfectSupportedFiberPrespectrumMap j ≫
        homotopyFiberProjection (Fibration.changeWeakPrespectrumMap (perfectOpenNested j)) =
      perfectSupportedInclusionPrespectrumMap j ∧
    IsStableEquivalence (perfectSupportedFiberPrespectrumMap j) ∧
    IsStableEquivalence (perfectSupportedFiberPrespectrumRebasedMap j) :=
  ⟨perfectOpenPrespectrum_isOmega j, perfectOpenPrespectrum_neg_subsingleton j,
    perfectOpenRestrictPrespectrumMap_succ_bijective_of_qcqs j,
    perfectOpenRestrictPrespectrumMap_zero_injective_of_qcqs j,
    ⟨perfectOpenOriginalRestrictionFlatHomotopy j⟩,
    perfectSupportedFiberPrespectrumMap_projection j,
    perfectSupportedFiberPrespectrumMap_isStableEquivalence j,
    perfectSupportedFiberPrespectrumRebasedMap_isStableEquivalence j⟩

/-- The qcqs fine boundary is the original relative boundary transported through the proved
positive equivalence. Its natural degree n starts at K_(n+1) of the open. -/
def perfectQcqsConnectingHom (n : ℕ) :
    (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K (n + 1) →*
      PerfectSupportedK j n := by
  letI : Fact (OpenDerivedImage.HasDerivedRoofs j) :=
    ⟨OpenDerivedImage.hasDerivedRoofs_of_qcqs j⟩
  exact perfectOpenFineConnectingHom j (OpenDerivedImage.hasPerfectComplements_of_qcqs j) n

/-- The fine boundary retains the original relative boundary, not just its image. -/
theorem perfectQcqsConnectingHom_comp_relative (n : ℕ) :
    (perfectQcqsConnectingHom j n).comp (perfectOpenKRestrict j (n + 1)) =
      perfectOpenConnectingHom j n := by
  let : Fact (OpenDerivedImage.HasDerivedRoofs j) :=
    ⟨OpenDerivedImage.hasDerivedRoofs_of_qcqs j⟩
  exact perfectOpenFineConnectingHom_comp_relative j
    (OpenDerivedImage.hasPerfectComplements_of_qcqs j) n

/-- Compatibility with the actual relative map determines the fine boundary uniquely. -/
theorem perfectQcqsConnectingHom_unique (n : ℕ)
    (δ : (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K (n + 1) →*
      PerfectSupportedK j n)
    (hδ : δ.comp (perfectOpenKRestrict j (n + 1)) = perfectOpenConnectingHom j n) :
    δ = perfectQcqsConnectingHom j n := by
  let : Fact (OpenDerivedImage.HasDerivedRoofs j) :=
    ⟨OpenDerivedImage.hasDerivedRoofs_of_qcqs j⟩
  exact perfectOpenFineConnectingHom_unique j
    (OpenDerivedImage.hasPerfectComplements_of_qcqs j) n δ hδ

/-- All three exact positions, including n = 0, use the existing restriction and inclusion. -/
theorem perfectQcqs_positiveLongExactSequence (n : ℕ) :
    (KMap (perfectComplexesRestrictOpenImmersion_isExact j) (n + 1)).range =
      (perfectQcqsConnectingHom j n).ker ∧
    (perfectQcqsConnectingHom j n).range = (perfectSupportedKMap j n).ker ∧
    (perfectSupportedKMap j n).range =
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) n).ker := by
  let : Fact (OpenDerivedImage.HasDerivedRoofs j) :=
    ⟨OpenDerivedImage.hasDerivedRoofs_of_qcqs j⟩
  exact perfectOpenFine_positiveLongExactSequence j
    (OpenDerivedImage.hasPerfectComplements_of_qcqs j) n

/-- The zero tail terminates surjectively in the actual restriction image only. -/
theorem perfectQcqs_zeroImageTail :
    (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 1).range =
      (perfectQcqsConnectingHom j 0).ker ∧
    (perfectQcqsConnectingHom j 0).range = (perfectSupportedKMap j 0).ker ∧
    (perfectSupportedKMap j 0).range = (perfectKZeroToOpenImage j).ker ∧
    Function.Surjective (perfectKZeroToOpenImage j) := by
  let : Fact (OpenDerivedImage.HasDerivedRoofs j) :=
    ⟨OpenDerivedImage.hasDerivedRoofs_of_qcqs j⟩
  exact perfectOpenFine_zeroImageTail j (OpenDerivedImage.hasPerfectComplements_of_qcqs j)

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0330"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenRestrictPrespectrumMap_succ_bijective_of_qcqs
  AlgebraicGeometry.Scheme.Modules.perfectOpenStableZeroImageEquivOfQcqs
  AlgebraicGeometry.Scheme.Modules.perfectOpenStableZeroImageEquivOfQcqs_coe
  AlgebraicGeometry.Scheme.Modules.perfectOpenRestrictPrespectrumMap_zero_injective_of_qcqs
  AlgebraicGeometry.Scheme.Modules.perfectQcqsConnectingHom
  AlgebraicGeometry.Scheme.Modules.perfectQcqs_positiveLongExactSequence
  AlgebraicGeometry.Scheme.Modules.perfectQcqs_zeroImageTail

attribute [colib_tag "COL-0330"]
  AlgebraicGeometry.Scheme.Modules.perfectQcqsConnectingHom_comp_relative
  AlgebraicGeometry.Scheme.Modules.perfectQcqsConnectingHom_unique
