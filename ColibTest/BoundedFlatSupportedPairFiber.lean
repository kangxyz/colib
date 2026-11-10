/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedPullbackPrespectrum

/-! The same canonical normalization, original K-maps and independent whole-path parameters. -/
noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS Topology Topology.LoopPrespectrum
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
open scoped unitInterval

universe u
variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.right = g ≫ j)


example : boundedAboveFlatPerfectSupportedPullback f ≅
    boundedAboveFlatPerfectSupportedPullbackNormalized f :=
  boundedAboveFlatPerfectSupportedPullbackNormalizationIso f

example : (boundedAboveFlatPerfectSupportedPullbackNormalized f).obj
  (boundedAboveFlatPerfectSupportedWaldhausen T.ι).zero =
    (boundedAboveFlatPerfectSupportedWaldhausen S.ι).zero :=
      (boundedAboveFlatPerfectSupportedPullbackNormalized_zero f)

example : boundedAboveFlatPerfectSupportedOpenKPullback j' j f g w 0 =
    KMap (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w) 0 :=
  boundedAboveFlatPerfectSupportedOpenKPullback_normalized j' j f g w 0

example : KMap (acyclicFunctor_exact (boundedAboveFlatPerfectSupportedOpenNested j T)
  (boundedAboveFlatPerfectSupportedOpenNested j' S)
  (boundedAboveFlatPerfectSupportedPullback_isExact f)
  (boundedAboveFlatPerfectSupportedOpenPullback_isExact j' j f g w)) 0 =
    KMap (acyclicFunctor_exact (boundedAboveFlatPerfectSupportedOpenNested j T)
      (boundedAboveFlatPerfectSupportedOpenNested j' S)
      (boundedAboveFlatPerfectSupportedPullback_isExact f).rebase
      (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w)) 0 :=
  boundedAboveFlatPerfectSupportedAcyclicKPullback_normalized j' j f g w 0

example :
    boundedAboveFlatPerfectSupportedFiberPullbackPrespectrumMap j' j f g w ≫
        homotopyFiberProjection (changeWeakPrespectrumMap
          (boundedAboveFlatPerfectSupportedOpenNested j' S)) =
      homotopyFiberProjection (changeWeakPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested
        j T)) ≫
        exactOriginalPrespectrumMap (boundedAboveFlatPerfectSupportedWaldhausen T.ι)
          (boundedAboveFlatPerfectSupportedWaldhausen S.ι)
          (boundedAboveFlatPerfectSupportedPullback_isExact f) :=
  boundedAboveFlatPerfectSupportedFiberPullbackPrespectrumMap_projection j' j f g w

example (n : ℕ)
    (x : (homotopyFiber (changeWeakPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j
      T))).space n) (s : unitInterval) :
    ((boundedAboveFlatPerfectSupportedFiberPullbackPrespectrumMap j' j f g w).map n x).1.2 s =
      (boundedAboveFlatPerfectSupportedOpenPullbackPrespectrumMap j' j f g w).map n (x.1.2 s) :=
  boundedAboveFlatPerfectSupportedFiberPullbackPrespectrumMap_path j' j f g w n x s

example (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j
      T))).space n) :
    (boundedAboveFlatPerfectSupportedOpenPullbackPrespectrumMap j' j f g w).map (n + 1)
        ((acyclicPrespectrumNullhomotopy (boundedAboveFlatPerfectSupportedOpenNested j T)).level (n
          + 1)
          (s, (originalPrespectrum (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j
            T))).structureMap n x t)) =
      (originalPrespectrum (boundedAboveFlatPerfectSupportedOpenNested j' S).coarse).structureMap n
        ((acyclicPrespectrumNullhomotopy (boundedAboveFlatPerfectSupportedOpenNested j' S)).level n
          (s, (originalPrespectrumMap (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested
            j T)) (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j' S))
            (acyclicFunctor_exact (boundedAboveFlatPerfectSupportedOpenNested j T)
              (boundedAboveFlatPerfectSupportedOpenNested j' S)
              (boundedAboveFlatPerfectSupportedPullback_isExact f).rebase
              (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w))
            (acyclicFunctor_zero (boundedAboveFlatPerfectSupportedOpenNested j T)
              (boundedAboveFlatPerfectSupportedOpenNested j' S)
              (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w)
              (boundedAboveFlatPerfectSupportedPullbackNormalized_zero f))).map
              n x)) t :=
  acyclicPrespectrumNullhomotopy_natural_structure (boundedAboveFlatPerfectSupportedOpenNested j T)
    (boundedAboveFlatPerfectSupportedOpenNested j' S)
    (boundedAboveFlatPerfectSupportedPullback_isExact f).rebase
    (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w)
      (boundedAboveFlatPerfectSupportedPullbackNormalized_zero f) n s t x

example (a : BoundedAboveFlatPerfectSupportedOpenK j T 0) :
    originalKStableEquiv (boundedAboveFlatPerfectSupportedOpenNested j' S).coarse 0
        (Additive.ofMul (boundedAboveFlatPerfectSupportedOpenKPullback j' j f g w 0 a)) =
      (stableHomotopyFunctor 0).map
        (boundedAboveFlatPerfectSupportedOpenPullbackPrespectrumMap j' j f g w)
        (originalKStableEquiv (boundedAboveFlatPerfectSupportedOpenNested j T).coarse 0
          (Additive.ofMul a)) :=
  boundedAboveFlatPerfectSupportedOpenPullbackPrespectrumMap_K_naturality j' j f g w 0 a

example (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        (boundedAboveFlatPerfectSupportedOpenPullbackPrespectrumMap j' j f g w) ≫
        stableFiberConnecting (changeWeakPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested
          j' S)) d =
      stableFiberConnecting (changeWeakPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j
        T)) d ≫
        (stableHomotopyFunctor d).map
          (boundedAboveFlatPerfectSupportedFiberPullbackPrespectrumMap j' j f g w) :=
  boundedAboveFlatPerfectSupportedStableConnecting_pullback j' j f g w d

example :
    (stableHomotopyFunctor ((-1 : ℤ) + 1)).map
        (boundedAboveFlatPerfectSupportedOpenPullbackPrespectrumMap j' j f g w) ≫
        stableFiberConnecting (changeWeakPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested
          j' S)) (-1) =
      stableFiberConnecting (changeWeakPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j
        T)) (-1) ≫
        (stableHomotopyFunctor (-1)).map
          (boundedAboveFlatPerfectSupportedFiberPullbackPrespectrumMap j' j f g w) :=
  boundedAboveFlatPerfectSupportedStableConnecting_pullback j' j f g w (-1)

example :
    canonicalFiberPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j T) ≫
        boundedAboveFlatPerfectSupportedFiberPullbackPrespectrumMap j' j f g w =
      originalPrespectrumMap (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j T))
        (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j' S))
        (acyclicFunctor_exact (boundedAboveFlatPerfectSupportedOpenNested j T)
          (boundedAboveFlatPerfectSupportedOpenNested j' S)
          (boundedAboveFlatPerfectSupportedPullback_isExact f).rebase
          (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w))
        (acyclicFunctor_zero (boundedAboveFlatPerfectSupportedOpenNested j T)
          (boundedAboveFlatPerfectSupportedOpenNested j' S)
          (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w)
          (boundedAboveFlatPerfectSupportedPullbackNormalized_zero f)) ≫
          canonicalFiberPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j' S) :=
  canonicalFiberPrespectrumMap_natural (boundedAboveFlatPerfectSupportedOpenNested j T)
    (boundedAboveFlatPerfectSupportedOpenNested j' S)
    (boundedAboveFlatPerfectSupportedPullback_isExact f).rebase
    (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w)
      (boundedAboveFlatPerfectSupportedPullbackNormalized_zero f)

