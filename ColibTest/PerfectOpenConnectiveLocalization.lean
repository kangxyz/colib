/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.PerfectOpenConnectiveLocalization
import Colib.AlgebraicGeometry.KTheory.PerfectOpenImagePrespectrum

/-! Regression signatures retain the actual boundary, maps, image subgroup and stable targets.
No qcqs geometry, arbitrary K-equivalence, or supported-image premise is silently supplied. -/

noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.OpenDerivedImage
open Topology.LoopPrespectrum

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

example : Function.Surjective (perfectKZeroToOpenImage j) :=
  perfectKZeroToOpenImage_surjective j

example (a : (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K 0) :
    (perfectKZeroToOpenImage j a :
      (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K 0) =
        KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0 a := rfl

example : IsStableEquivalence
    (Fibration.canonicalFiberPrespectrumMap (perfectOpenNested j)) :=
  perfectOpen_canonicalFiberPrespectrumMap_isStableEquivalence j

example (k : ℤ) (hk : k < 0) :
    Subsingleton (stableHomotopyGroup (perfectOpenPrespectrum j) k) :=
  perfectOpenPrespectrum_neg_subsingleton j k hk

example (n : ℕ) (a : PerfectOpenK j n) :
    originalKStableEquiv (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace) n
        (Additive.ofMul (perfectOpenKRestrict j n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (perfectOpenRestrictPrespectrumMap j)
        (originalKStableEquiv (perfectOpenWeakWaldhausen j) n (Additive.ofMul a)) :=
  perfectOpenRestrictPrespectrumMap_naturality j n a

example (b : (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K 0) :
    (∃ a : stableHomotopyGroup (perfectOpenPrespectrum j) 0,
      (stableHomotopyFunctor 0).map (perfectOpenRestrictPrespectrumMap j) a =
        originalKStableEquiv (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace) 0
          (Additive.ofMul b)) ↔
      b ∈ (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0).range :=
  perfectOpenRestrictPrespectrumMap_zero_mem_range_iff j b

variable [HasDerivedCategory.{d} U.Modules] [Fact (HasDerivedRoofs j)]
  (hc : HasPerfectComplements j)

example (n : ℕ) :
    perfectOpenFineConnectingHom j hc n =
      (perfectOpenConnectingHom j n).comp (relativeKRestrictEquiv j hc n).symm.toMonoidHom :=
  rfl

example (n : ℕ) :
    (perfectOpenFineConnectingHom j hc n).comp (perfectOpenKRestrict j (n + 1)) =
      perfectOpenConnectingHom j n := perfectOpenFineConnectingHom_comp_relative j hc n

example (n : ℕ) :
    (KMap (perfectComplexesRestrictOpenImmersion_isExact j) (n + 1)).range =
      (perfectOpenFineConnectingHom j hc n).ker ∧
    (perfectOpenFineConnectingHom j hc n).range = (perfectSupportedKMap j n).ker ∧
    (perfectSupportedKMap j n).range =
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) n).ker :=
  perfectOpenFine_positiveLongExactSequence j hc n

example :
    (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 1).range =
      (perfectOpenFineConnectingHom j hc 0).ker ∧
    (perfectOpenFineConnectingHom j hc 0).range = (perfectSupportedKMap j 0).ker ∧
    (perfectSupportedKMap j 0).range = (perfectKZeroToOpenImage j).ker ∧
    Function.Surjective (perfectKZeroToOpenImage j) :=
  perfectOpenFine_zeroImageTail j hc

example (n : ℕ)
    (δ : (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K (n + 1) →*
      PerfectSupportedK j n)
    (hδ : δ.comp (perfectOpenKRestrict j (n + 1)) = perfectOpenConnectingHom j n) :
    δ = perfectOpenFineConnectingHom j hc n := perfectOpenFineConnectingHom_unique j hc n δ hδ

example :
    (relativeKZeroImageEquiv j hc).toMonoidHom.comp (perfectOpenKMap j 0) =
      perfectKZeroToOpenImage j := relativeKZeroImageEquiv_comp_perfectOpenKMap j hc

example (n : ℕ) : Function.Bijective
    ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map (perfectOpenRestrictPrespectrumMap j)) :=
  perfectOpenRestrictPrespectrumMap_succ_bijective j hc n

example : Function.Injective
    ((stableHomotopyFunctor 0).map (perfectOpenRestrictPrespectrumMap j)) :=
  perfectOpenRestrictPrespectrumMap_zero_injective j hc

example (a : stableHomotopyGroup (perfectOpenPrespectrum j) 0) :
    originalKStableEquiv (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace) 0
        (Additive.ofMul ((perfectOpenStableZeroImageEquiv j hc a).toMul :
          (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K 0)) =
      (stableHomotopyFunctor 0).map (perfectOpenRestrictPrespectrumMap j) a :=
  perfectOpenStableZeroImageEquiv_coe j hc a
