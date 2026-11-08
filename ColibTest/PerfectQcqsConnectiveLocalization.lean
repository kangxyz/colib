/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.PerfectQcqsConnectiveLocalization

/-! Full-signature qcqs endpoint consumers. No roof or complement hypothesis is supplied. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology Topology.LoopPrespectrum AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u d
variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j] [HasDerivedCategory.{d} U.Modules]

example (n : ℕ) : Function.Bijective
    ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map (perfectOpenRestrictPrespectrumMap j)) :=
  perfectOpenRestrictPrespectrumMap_succ_bijective_of_qcqs j n

example : Function.Injective
    ((stableHomotopyFunctor 0).map (perfectOpenRestrictPrespectrumMap j)) :=
  perfectOpenRestrictPrespectrumMap_zero_injective_of_qcqs j

example : stableHomotopyGroup (perfectOpenPrespectrum j) 0 ≃+
    Additive (PerfectOpenKZeroImage j) := perfectOpenStableZeroImageEquivOfQcqs j

example (a : stableHomotopyGroup (perfectOpenPrespectrum j) 0) :
    originalKStableEquiv (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace) 0
        (Additive.ofMul ((perfectOpenStableZeroImageEquivOfQcqs j a).toMul :
          (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K 0)) =
      (stableHomotopyFunctor 0).map (perfectOpenRestrictPrespectrumMap j) a :=
  perfectOpenStableZeroImageEquivOfQcqs_coe j a

example (b : (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K 0) :
    (∃ a : stableHomotopyGroup (perfectOpenPrespectrum j) 0,
      (stableHomotopyFunctor 0).map (perfectOpenRestrictPrespectrumMap j) a =
        originalKStableEquiv (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace) 0
          (Additive.ofMul b)) ↔ b ∈ PerfectOpenKZeroImage j :=
  perfectOpenRestrictPrespectrumMap_zero_mem_range_iff j b

example (n : ℕ) :
    (KMap (perfectComplexesRestrictOpenImmersion_isExact j) (n + 1)).range =
      (perfectQcqsConnectingHom j n).ker ∧
    (perfectQcqsConnectingHom j n).range = (perfectSupportedKMap j n).ker ∧
    (perfectSupportedKMap j n).range =
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) n).ker :=
  perfectQcqs_positiveLongExactSequence j n

example :
    (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 1).range =
      (perfectQcqsConnectingHom j 0).ker ∧
    (perfectQcqsConnectingHom j 0).range = (perfectSupportedKMap j 0).ker ∧
    (perfectSupportedKMap j 0).range = (perfectKZeroToOpenImage j).ker ∧
    Function.Surjective (perfectKZeroToOpenImage j) :=
  perfectQcqs_zeroImageTail j

example : IsOmega (perfectOpenPrespectrum j) ∧
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
  perfectQcqs_connectiveImageCoverLocalization j

example (n : ℕ) :
    (perfectQcqsConnectingHom j n).comp (perfectOpenKRestrict j (n + 1)) =
      perfectOpenConnectingHom j n := perfectQcqsConnectingHom_comp_relative j n

example (n : ℕ)
    (δ : (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K (n + 1) →*
      PerfectSupportedK j n)
    (hδ : δ.comp (perfectOpenKRestrict j (n + 1)) = perfectOpenConnectingHom j n) :
    δ = perfectQcqsConnectingHom j n := perfectQcqsConnectingHom_unique j n δ hδ
