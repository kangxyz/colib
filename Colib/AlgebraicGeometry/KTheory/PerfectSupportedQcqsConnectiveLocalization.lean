/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenImagePrespectrum
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedUnionFiberComparison
public import Colib.AlgebraicGeometry.KTheory.SupportedOpenFineLocalization

/-!
# Fixed-pair supported connective image-cover localization

For an open immersion j and an auxiliary open T in a qcqs scheme X, compactness of
j.opensRange ⊔ T suffices. The actual supported coarse S-prespectrum is the connective
image cover. Its actual union-supported fiber map retains the full acyclic path and both
independent structure/time parameters. The fine K1-to-K0 tail is the existing supported
sequence, imported above without replacing its maps.

This is the fixed-pair additional-support form of TT 5.1.2 in the stated compact-union
setting, following TT 5.2. Support means ambient perfect complexes acyclic on the named
open, not perfect complexes on a closed subscheme. Support-forgetting boundary naturality,
arbitrary global-pair naturality and Bass nonconnective TT 7.4 remain outside this result.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology Topology.LoopPrespectrum
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  (hW : IsCompact ((j.opensRange ⊔ T : X.Opens) : Set X))

include hW in
/-- The actual supported coarse model, actual restriction image and full canonical fiber
lift form the fixed-pair connective localization. No spectrum profile is supplied as data. -/
@[colib_tag "COL-0335",
  colib_ref "ThomasonTrobaugh1990" "Theorem 5.1.2 and proof 5.2, pp. 337-338" "adaptation"
    "Fixed supported pair with compact union, actual connective coarse image cover and fiber"]
theorem perfectSupportedQcqs_connectiveImageCoverLocalization :
    IsOmega (perfectSupportedOpenPrespectrum j T) ∧
    (∀ k : ℤ, k < 0 →
      Subsingleton (stableHomotopyGroup (perfectSupportedOpenPrespectrum j T) k)) ∧
    (∀ n : ℕ, Function.Bijective ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
      (perfectSupportedOpenRestrictPrespectrumMap j T))) ∧
    Function.Injective ((stableHomotopyFunctor 0).map
      (perfectSupportedOpenRestrictPrespectrumMap j T)) ∧
    (∀ b : PerfectSupportedK (j ⁻¹ᵁ T).ι 0,
      (∃ a : stableHomotopyGroup (perfectSupportedOpenPrespectrum j T) 0,
        (stableHomotopyFunctor 0).map (perfectSupportedOpenRestrictPrespectrumMap j T) a =
          originalKStableEquiv (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) 0
            (Additive.ofMul b)) ↔ b ∈ PerfectSupportedOpenKZeroImage j T) ∧
    Nonempty (Homotopy
      (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T) ≫
        perfectSupportedOpenRestrictPrespectrumMap j T)
      (perfectSupportedRestrictPrespectrumMap j T)) ∧
    perfectSupportedUnionFiberPrespectrumMap j T ≫
        homotopyFiberProjection (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j
          T)) =
      perfectSupportedUnionInclusionPrespectrumMap j T ∧
    (∀ (n : ℕ) (x : (perfectSupportedUnionPrespectrum j T).space n) (s : unitInterval),
      ((perfectSupportedUnionFiberPrespectrumMap j T).map n x).1.2 s =
        (perfectSupportedUnionPrespectrumNullhomotopy j T).level n (s, x)) ∧
    (∀ (n : ℕ) (s t : unitInterval) (x : (perfectSupportedUnionPrespectrum j T).space n),
      (perfectSupportedUnionPrespectrumNullhomotopy j T).level (n + 1)
          (s, (perfectSupportedUnionPrespectrum j T).structureMap n x t) =
        (perfectSupportedOpenPrespectrum j T).structureMap n
          ((perfectSupportedUnionPrespectrumNullhomotopy j T).level n (s, x)) t) ∧
    IsStableEquivalence (perfectSupportedUnionFiberPrespectrumMap j T) ∧
    IsStableEquivalence (perfectSupportedUnionFiberPrespectrumRebasedMap j T) :=
  ⟨perfectSupportedOpenPrespectrum_isOmega j T,
    perfectSupportedOpenPrespectrum_neg_subsingleton j T,
    perfectSupportedOpenRestrictPrespectrumMap_succ_bijective_of_union_compact j T hW,
    perfectSupportedOpenRestrictPrespectrumMap_zero_injective_of_union_compact j T hW,
    perfectSupportedOpenRestrictPrespectrumMap_zero_mem_range_iff j T,
    ⟨perfectSupportedOpenRestrictionHomotopy j T⟩,
    perfectSupportedUnionFiberPrespectrumMap_projection j T,
    perfectSupportedUnionFiberPrespectrumMap_path j T,
    perfectSupportedUnionPrespectrumNullhomotopy_structure j T,
    perfectSupportedUnionFiberPrespectrumMap_isStableEquivalence j T,
    perfectSupportedUnionFiberPrespectrumRebasedMap_isStableEquivalence j T⟩

/-- Compactness of both opens gives the same positive actual stable comparison. -/
theorem perfectSupportedOpenRestrictPrespectrumMap_succ_bijective_of_qcqs [CompactSpace U]
    (hT : IsCompact (T : Set X)) (n : ℕ) :
    Function.Bijective ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
      (perfectSupportedOpenRestrictPrespectrumMap j T)) :=
  perfectSupportedOpenRestrictPrespectrumMap_succ_bijective_of_union_compact j T
    (isCompact_supportedUnion j T hT) n

/-- Compactness of both opens gives the same exact stable-zero image equivalence. -/
def perfectSupportedOpenStableZeroImageEquivOfQcqs [CompactSpace U]
    (hT : IsCompact (T : Set X)) :
    stableHomotopyGroup (perfectSupportedOpenPrespectrum j T) 0 ≃+
      Additive (PerfectSupportedOpenKZeroImage j T) :=
  perfectSupportedOpenStableZeroImageEquivOfUnionCompact j T
    (isCompact_supportedUnion j T hT)

end AlgebraicGeometry.Scheme.Modules
