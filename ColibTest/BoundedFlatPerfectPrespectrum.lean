/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumPullback
public import Colib.AlgebraicGeometry.KTheory.PerfectPullbackCompatibility

/-! Full public consumers of the actual inclusion, stable and zero-space K maps,
whole normalized pullback square, and independent loop/structure parameters. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

example (X : RingedSpace.{u, u}) :
    boundedAboveFlatPerfectToPerfectPrespectrumMap X =
      exactOriginalPrespectrumMap (boundedAboveFlatPerfectWaldhausen X)
        (perfectComplexesWaldhausen X) (boundedAboveFlatPerfectInclusion_isExact X) := rfl

example (X : RingedSpace.{u, u}) [CompactSpace X.carrier] :
    IsStableEquivalence (boundedAboveFlatPerfectToPerfectPrespectrumMap X) :=
  boundedAboveFlatPerfectToPerfectPrespectrumMap_isStableEquivalence X

example (R : CommRingCat.{u}) :
    IsStableEquivalence
      (boundedAboveFlatPerfectToPerfectPrespectrumMap
        (Scheme.Spec.obj (Opposite.op R)).toRingedSpace) :=
  boundedAboveFlatPerfectSpecPrespectrumMap_isStableEquivalence R

example (X : RingedSpace.{u, u}) (n : ℕ) (a : X.boundedAboveFlatPerfectK n) :
    originalKStableEquiv (perfectComplexesWaldhausen X) n
        (Additive.ofMul (boundedAboveFlatPerfectToPerfectKMap X n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (boundedAboveFlatPerfectToPerfectPrespectrumMap X)
        (originalKStableEquiv (boundedAboveFlatPerfectWaldhausen X) n (Additive.ofMul a)) :=
  boundedAboveFlatPerfectToPerfectPrespectrumMap_originalK_naturality X n a

example (X : RingedSpace.{u, u}) (n : ℕ) (a : X.boundedAboveFlatPerfectK n) :
    originalZeroSpaceEquiv (perfectComplexesWaldhausen X) n
        (boundedAboveFlatPerfectToPerfectKMap X n a) =
      HomotopyGroup.map ((boundedAboveFlatPerfectToPerfectPrespectrumMap X).map 0)
        ((boundedAboveFlatPerfectToPerfectPrespectrumMap X).map_point 0)
        (originalZeroSpaceEquiv (boundedAboveFlatPerfectWaldhausen X) n a) :=
  boundedAboveFlatPerfectToPerfectPrespectrumMap_zeroSpace_naturality X n a

example (X : RingedSpace.{u, u}) [CompactSpace X.carrier] (n : ℕ) :
    (↑(boundedAboveFlatPerfectKEquiv X n) : X.boundedAboveFlatPerfectK n →*
        (perfectComplexesWaldhausen X).K n) =
      boundedAboveFlatPerfectToPerfectKMap X n := rfl

example (X : RingedSpace.{u, u}) (a : X.boundedAboveFlatPerfectK 0) :
    originalKStableEquiv (perfectComplexesWaldhausen X) 0
        (Additive.ofMul (boundedAboveFlatPerfectToPerfectKMap X 0 a)) =
      (stableHomotopyFunctor (0 : ℤ)).map (boundedAboveFlatPerfectToPerfectPrespectrumMap X)
        (originalKStableEquiv (boundedAboveFlatPerfectWaldhausen X) 0 (Additive.ofMul a)) :=
  boundedAboveFlatPerfectToPerfectPrespectrumMap_originalK_naturality X 0 a

example (X : RingedSpace.{u, u}) (a : X.boundedAboveFlatPerfectK 0) :
    originalZeroSpaceEquiv (perfectComplexesWaldhausen X) 0
        (boundedAboveFlatPerfectToPerfectKMap X 0 a) =
      HomotopyGroup.map ((boundedAboveFlatPerfectToPerfectPrespectrumMap X).map 0)
        ((boundedAboveFlatPerfectToPerfectPrespectrumMap X).map_point 0)
        (originalZeroSpaceEquiv (boundedAboveFlatPerfectWaldhausen X) 0 a) :=
  boundedAboveFlatPerfectToPerfectPrespectrumMap_zeroSpace_naturality X 0 a

example (X : RingedSpace.{u, u}) [CompactSpace X.carrier] :
    (↑(boundedAboveFlatPerfectKEquiv X 0) : X.boundedAboveFlatPerfectK 0 →*
        (perfectComplexesWaldhausen X).K 0) =
      boundedAboveFlatPerfectToPerfectKMap X 0 := rfl

example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    boundedAboveFlatPerfectPullbackPrespectrumMap f =
      exactOriginalPrespectrumMap _ _ (boundedAboveFlatPerfectPullback_isExact f) := rfl

example {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (K : (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory) :
    ((boundedAboveFlatPerfectInclusionFlatPullbackIso f).hom.app K).hom = 𝟙 _ := rfl

example {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    LoopPrespectrum.Homotopy
      (boundedAboveFlatPerfectToPerfectPrespectrumMap Y.toRingedSpace ≫ perfectFlatPrespectrumMap f)
      (boundedAboveFlatPerfectPullbackPrespectrumMap f ≫
        boundedAboveFlatPerfectToPerfectPrespectrumMap X.toRingedSpace) :=
  boundedAboveFlatPerfectPullbackPrespectrumHomotopy f

example {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (boundedAboveFlatPerfectPullbackPrespectrumHomotopy f).level n (0, x) =
      (boundedAboveFlatPerfectToPerfectPrespectrumMap Y.toRingedSpace ≫ perfectFlatPrespectrumMap f).map n x :=
  (boundedAboveFlatPerfectPullbackPrespectrumHomotopy f).at_zero n x

example {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (boundedAboveFlatPerfectPullbackPrespectrumHomotopy f).level n (1, x) =
      (boundedAboveFlatPerfectPullbackPrespectrumMap f ≫ boundedAboveFlatPerfectToPerfectPrespectrumMap X.toRingedSpace).map n x :=
  (boundedAboveFlatPerfectPullbackPrespectrumHomotopy f).at_one n x

example {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (n : ℕ) (s : unitInterval) :
    (boundedAboveFlatPerfectPullbackPrespectrumHomotopy f).level n
        (s, (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).point n) =
      (originalPrespectrum (perfectComplexesWaldhausen X.toRingedSpace)).point n :=
  boundedAboveFlatPerfectPullbackPrespectrumHomotopy_at_point f n s

example {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n)
    (t : unitInterval) :
    (boundedAboveFlatPerfectPullbackPrespectrumHomotopy f).level (n + 1)
        (s, (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).structureMap
          n x t) =
      (originalPrespectrum (perfectComplexesWaldhausen X.toRingedSpace)).structureMap n
        ((boundedAboveFlatPerfectPullbackPrespectrumHomotopy f).level n (s, x)) t :=
  boundedAboveFlatPerfectPullbackPrespectrumHomotopy_comm f n s x t

example {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space 0) :
    (boundedAboveFlatPerfectPullbackPrespectrumHomotopy f).level 0 (0, x) =
      (boundedAboveFlatPerfectToPerfectPrespectrumMap Y.toRingedSpace ≫ perfectFlatPrespectrumMap f).map 0 x :=
  (boundedAboveFlatPerfectPullbackPrespectrumHomotopy f).at_zero 0 x

example {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space 0) :
    (boundedAboveFlatPerfectPullbackPrespectrumHomotopy f).level 0 (1, x) =
      (boundedAboveFlatPerfectPullbackPrespectrumMap f ≫ boundedAboveFlatPerfectToPerfectPrespectrumMap X.toRingedSpace).map 0 x :=
  (boundedAboveFlatPerfectPullbackPrespectrumHomotopy f).at_one 0 x

example {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (s : unitInterval) :
    (boundedAboveFlatPerfectPullbackPrespectrumHomotopy f).level 0
        (s, (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).point 0) =
      (originalPrespectrum (perfectComplexesWaldhausen X.toRingedSpace)).point 0 :=
  boundedAboveFlatPerfectPullbackPrespectrumHomotopy_at_point f 0 s

example {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space 0)
    (t : unitInterval) :
    (boundedAboveFlatPerfectPullbackPrespectrumHomotopy f).level (0 + 1)
        (s, (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).structureMap
          0 x t) =
      (originalPrespectrum (perfectComplexesWaldhausen X.toRingedSpace)).structureMap 0
        ((boundedAboveFlatPerfectPullbackPrespectrumHomotopy f).level 0 (s, x)) t :=
  boundedAboveFlatPerfectPullbackPrespectrumHomotopy_comm f 0 s x t

example (X : RingedSpace.{u, u}) :
    (CategoryTheory.rebaseFunctor (boundedAboveFlatPerfectInclusion X)
      (boundedAboveFlatPerfectWaldhausen X).zero (perfectComplexesWaldhausen X).zero
      (((boundedAboveFlatPerfectInclusion_isExact X).zero
        (boundedAboveFlatPerfectWaldhausen X).isZero).iso
          (perfectComplexesWaldhausen X).isZero)).obj
            (boundedAboveFlatPerfectWaldhausen X).zero =
              (perfectComplexesWaldhausen X).zero :=
  CategoryTheory.rebaseFunctor_obj_base _ _ _ _

example (R : CommRingCat.{u}) (n : ℕ)
    (a : (Scheme.Spec.obj (Opposite.op R)).toRingedSpace.boundedAboveFlatPerfectK n) :
    originalKStableEquiv
        (perfectComplexesWaldhausen (Scheme.Spec.obj (Opposite.op R)).toRingedSpace) n
        (Additive.ofMul
          (boundedAboveFlatPerfectToPerfectKMap (Scheme.Spec.obj (Opposite.op R)).toRingedSpace n a)) =
      (stableHomotopyFunctor (n : ℤ)).map
        (boundedAboveFlatPerfectToPerfectPrespectrumMap
          (Scheme.Spec.obj (Opposite.op R)).toRingedSpace)
        (originalKStableEquiv
          (boundedAboveFlatPerfectWaldhausen (Scheme.Spec.obj (Opposite.op R)).toRingedSpace) n
          (Additive.ofMul a)) :=
  boundedAboveFlatPerfectToPerfectPrespectrumMap_originalK_naturality _ n a

example {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (n : ℕ) :
    (Waldhausen.KMap (perfectFlatPullback_waldhausenExact f) n).comp
        (boundedAboveFlatPerfectToPerfectKMap Y.toRingedSpace n) =
      (boundedAboveFlatPerfectToPerfectKMap X.toRingedSpace n).comp
        (Waldhausen.KMap (boundedAboveFlatPerfectPullback_isExact f) n) :=
  AlgebraicGeometry.Scheme.boundedAboveFlatPerfectToPerfectKMap_flatPullback f n

example {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (Waldhausen.KMap (perfectFlatPullback_waldhausenExact f) 0).comp
        (boundedAboveFlatPerfectToPerfectKMap Y.toRingedSpace 0) =
      (boundedAboveFlatPerfectToPerfectKMap X.toRingedSpace 0).comp
        (Waldhausen.KMap (boundedAboveFlatPerfectPullback_isExact f) 0) :=
  AlgebraicGeometry.Scheme.boundedAboveFlatPerfectToPerfectKMap_flatPullback f 0
