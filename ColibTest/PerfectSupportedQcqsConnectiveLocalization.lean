/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.PerfectSupportedQcqsConnectiveLocalization

/-! Full-signature consumers for the actual supported spectrum maps and image-cover endpoint. -/

noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology Topology.LoopPrespectrum AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

example : perfectSupportedUnionPrespectrum j T ≅
    originalPrespectrum (Fibration.acyclicStructure (perfectSupportedOpenNested j T)) :=
  perfectSupportedUnionAcyclicPrespectrumIso j T

example :
    perfectSupportedUnionToAcyclicPrespectrumMap j T ≫
      Fibration.acyclicInclusionPrespectrumMap (perfectSupportedOpenNested j T) =
        perfectSupportedUnionInclusionPrespectrumMap j T  :=
  perfectSupportedUnionToAcyclicPrespectrumMap_inclusion j T

example (n : ℕ)
    (s : unitInterval) (x : (perfectSupportedUnionPrespectrum j T).space n) :
    (perfectSupportedUnionPrespectrumNullhomotopy j T).level n (s, x) =
      (Fibration.acyclicPrespectrumNullhomotopy (perfectSupportedOpenNested j T)).level n
        (s, (perfectSupportedUnionToAcyclicPrespectrumMap j T).map n x)  :=
  perfectSupportedUnionPrespectrumNullhomotopy_level j T n s x

example :
    perfectSupportedUnionFiberPrespectrumMap j T ≫
      homotopyFiberProjection (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j
        T)) =
        perfectSupportedUnionInclusionPrespectrumMap j T  :=
  perfectSupportedUnionFiberPrespectrumMap_projection j T

example (n : ℕ)
    (x : (perfectSupportedUnionPrespectrum j T).space n) (s : unitInterval) :
    ((perfectSupportedUnionFiberPrespectrumMap j T).map n x).1.2 s =
      (perfectSupportedUnionPrespectrumNullhomotopy j T).level n (s, x)  :=
  perfectSupportedUnionFiberPrespectrumMap_path j T n x s

example :
    perfectSupportedUnionFiberPrespectrumMap j T =
      homotopyFiberLift (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T))
        (perfectSupportedUnionInclusionPrespectrumMap j T)
        (perfectSupportedUnionPrespectrumNullhomotopy j T)  :=
  perfectSupportedUnionFiberPrespectrumMap_eq_lift j T

example (n : ℕ)
    (s t : unitInterval) (x : (perfectSupportedUnionPrespectrum j T).space n) :
    (perfectSupportedUnionPrespectrumNullhomotopy j T).level (n + 1)
        (s, (perfectSupportedUnionPrespectrum j T).structureMap n x t) =
      (perfectSupportedOpenPrespectrum j T).structureMap n
        ((perfectSupportedUnionPrespectrumNullhomotopy j T).level n (s, x)) t  :=
  perfectSupportedUnionPrespectrumNullhomotopy_structure j T n s t x

example :
    IsStableEquivalence (perfectSupportedUnionFiberPrespectrumMap j T)  :=
  perfectSupportedUnionFiberPrespectrumMap_isStableEquivalence j T

example (n : ℕ)
    (a : PerfectSupportedK (T ⊔ j.opensRange).ι n) :
    originalKStableEquiv (perfectSupportedWaldhausen T.ι) n
        (Additive.ofMul (perfectSupportedUnionKMap j T n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (perfectSupportedUnionInclusionPrespectrumMap j T)
        (originalKStableEquiv (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι) n (Additive.ofMul
          a))  :=
  perfectSupportedUnionInclusionPrespectrumMap_naturality j T n a

example (n : ℕ) :
    HomotopyGroup.piMap n (perfectSupportedUnionFiberMap j T)
      (perfectSupportedUnionFiberMap_basepoint j T) = perfectSupportedUnionFiberKMap j T n  :=
  perfectSupportedUnionFiberMap_piMap j T n

example :
    (Fibration.originalFiberToSpectrumLevelOne (perfectSupportedOpenNested j
      T)).toHomotopyEquiv.toFun.comp
        (perfectSupportedUnionFiberMap j T) =
      ((perfectSupportedUnionFiberPrespectrumMap j T).map 1).comp
        (perfectSupportedWaldhausen (T ⊔
          j.opensRange).ι).asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun  :=
  perfectSupportedUnionFiberPrespectrumMap_level_one_square j T

example :
    LoopPrespectrum.Homotopy (perfectSupportedUnionFiberPrespectrumRebasedMap j T)
      (perfectSupportedUnionFiberPrespectrumMap j T)  :=
  perfectSupportedUnionFiberPrespectrumRebaseHomotopy j T

example :
    IsStableEquivalence (perfectSupportedUnionFiberPrespectrumRebasedMap j T)  :=
  perfectSupportedUnionFiberPrespectrumRebasedMap_isStableEquivalence j T

example :
    LoopPrespectrum.Homotopy
      (perfectSupportedUnionFiberPrespectrumRebasedMap j T ≫
        homotopyFiberProjection (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j
          T)))
      (exactOriginalPrespectrumMap (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι)
        (perfectSupportedWaldhausen T.ι)
        ((perfectSupportedUnionToAcyclic_exact j T).comp
      (Fibration.acyclicInclusion_exact (perfectSupportedOpenNested j T))))  :=
  perfectSupportedUnionFiberPrespectrumRebasedMapProjectionHomotopy j T

example : Homotopy
    (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T) ≫
      perfectSupportedOpenRestrictPrespectrumMap j T)
    (perfectSupportedRestrictPrespectrumMap j T)  :=
  perfectSupportedOpenRestrictionHomotopy j T

example (k : ℤ) :
    (stableHomotopyFunctor k).map
        (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T)) ≫
      (stableHomotopyFunctor k).map (perfectSupportedOpenRestrictPrespectrumMap j T) =
        (stableHomotopyFunctor k).map (perfectSupportedRestrictPrespectrumMap j T)  :=
  perfectSupportedOpenRestrictPrespectrumMap_comp_stable j T k

example (n : ℕ)
    (a : PerfectSupportedOpenCoarseK j T n) :
    originalKStableEquiv (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) n
        (Additive.ofMul (perfectSupportedOpenKRestrict j T n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (perfectSupportedOpenRestrictPrespectrumMap j T)
        (originalKStableEquiv (perfectSupportedOpenWeakWaldhausen j T) n (Additive.ofMul a))  :=
  perfectSupportedOpenRestrictPrespectrumMap_naturality j T n a

example (n : ℕ)
    (a : PerfectSupportedK T.ι n) :
    originalKStableEquiv (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) n
        (Additive.ofMul (perfectSupportedKRestrict j T n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (perfectSupportedRestrictPrespectrumMap j T)
        (originalKStableEquiv (perfectSupportedWaldhausen T.ι) n (Additive.ofMul a))  :=
  perfectSupportedRestrictPrespectrumMap_naturality j T n a

example
    (b : (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).K 0) :
    (∃ a : stableHomotopyGroup (perfectSupportedOpenPrespectrum j T) 0,
      (stableHomotopyFunctor 0).map (perfectSupportedOpenRestrictPrespectrumMap j T) a =
        originalKStableEquiv (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) 0
          (Additive.ofMul b)) ↔ b ∈ PerfectSupportedOpenKZeroImage j T  :=
  perfectSupportedOpenRestrictPrespectrumMap_zero_mem_range_iff j T b

-- The structure square explicitly covers n = 0 with independent time parameters.
example (s t : unitInterval) (x : (perfectSupportedUnionPrespectrum j T).space 0) :
    (perfectSupportedUnionPrespectrumNullhomotopy j T).level 1
        (s, (perfectSupportedUnionPrespectrum j T).structureMap 0 x t) =
      (perfectSupportedOpenPrespectrum j T).structureMap 0
        ((perfectSupportedUnionPrespectrumNullhomotopy j T).level 0 (s, x)) t :=
  perfectSupportedUnionPrespectrumNullhomotopy_structure j T 0 s t x

variable [CompactSpace X] [QuasiSeparatedSpace X]
  (hW : IsCompact ((j.opensRange ⊔ T : X.Opens) : Set X))

example (n : ℕ) :
    Function.Bijective ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
      (perfectSupportedOpenRestrictPrespectrumMap j T))  :=
  perfectSupportedOpenRestrictPrespectrumMap_succ_bijective_of_union_compact j T hW n

example :
    stableHomotopyGroup (perfectSupportedOpenPrespectrum j T) 0 ≃+ Additive
      (PerfectSupportedOpenKZeroImage j T)  :=
  perfectSupportedOpenStableZeroImageEquivOfUnionCompact j T hW

example
    (a : stableHomotopyGroup (perfectSupportedOpenPrespectrum j T) 0) :
    originalKStableEquiv (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) 0
        (Additive.ofMul ((perfectSupportedOpenStableZeroImageEquivOfUnionCompact j T hW a).toMul :
          (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).K 0)) =
      (stableHomotopyFunctor 0).map (perfectSupportedOpenRestrictPrespectrumMap j T) a  :=
  perfectSupportedOpenStableZeroImageEquivOfUnionCompact_coe j T hW a

example :
    Function.Injective ((stableHomotopyFunctor 0).map (perfectSupportedOpenRestrictPrespectrumMap
      j T))  :=
  perfectSupportedOpenRestrictPrespectrumMap_zero_injective_of_union_compact j T hW

example :
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
    IsStableEquivalence (perfectSupportedUnionFiberPrespectrumRebasedMap j T)  :=
  perfectSupportedQcqs_connectiveImageCoverLocalization j T hW

-- Existing fine K1-to-K0 tail, with the unchanged support labels and maps.
example :
    (perfectSupportedKRestrict j T 1).range =
      (perfectSupportedConnectingHomOfUnionCompact j T hW 0).ker ∧
    (perfectSupportedConnectingHomOfUnionCompact j T hW 0).range =
      (perfectSupportedUnionKMap j T 0).ker ∧
    (perfectSupportedUnionKMap j T 0).range =
      (perfectSupportedKRestrict j T 0).ker :=
  perfectSupported_zeroTail_of_union_compact j T hW
