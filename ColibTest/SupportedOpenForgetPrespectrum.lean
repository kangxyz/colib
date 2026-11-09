/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenForgetStableBoundary

/-! # Full-signature consumers of whole-prespectrum support forgetting -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open Topology Topology.LoopPrespectrum
open scoped unitInterval

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

example :
    Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T) ≫
        perfectSupportedOpenForgetPrespectrumMap j T =
      perfectSupportedInclusionPrespectrumMap T.ι ≫
        Fibration.changeWeakPrespectrumMap (perfectOpenNested j) :=
  perfectSupportedOpenForgetPrespectrumMap_changeWeak j T

example :
    perfectSupportedUnionInclusionPrespectrumMap j T ≫
        perfectSupportedInclusionPrespectrumMap T.ι =
      perfectSupportedUnionForgetPrespectrumMap j T ≫
        perfectSupportedInclusionPrespectrumMap j :=
  perfectSupportedUnionForgetPrespectrumMap_inclusion j T

example : LoopPrespectrum.Homotopy
    (perfectSupportedOpenForgetPrespectrumMap j T ≫ perfectOpenRestrictPrespectrumMap j)
    (perfectSupportedOpenRestrictPrespectrumMap j T ≫
      perfectSupportedInclusionPrespectrumMap (j ⁻¹ᵁ T).ι) :=
  perfectSupportedOpenForgetPrespectrumRestrictHomotopy j T

example :
    perfectSupportedOpenForgetFiberPrespectrumMap j T ≫
        homotopyFiberProjection (Fibration.changeWeakPrespectrumMap (perfectOpenNested j)) =
      homotopyFiberProjection
        (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T)) ≫
          perfectSupportedInclusionPrespectrumMap T.ι :=
  perfectSupportedOpenForgetFiberPrespectrumMap_projection j T

example (n : ℕ)
    (z : (homotopyFiber
      (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T))).space n)
    (s : unitInterval) :
    ((perfectSupportedOpenForgetFiberPrespectrumMap j T).map n z).1.2 s =
      (perfectSupportedOpenForgetPrespectrumMap j T).map n (z.1.2 s) :=
  perfectSupportedOpenForgetFiberPrespectrumMap_path j T n z s

example (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (perfectSupportedOpenForgetPrespectrumMap j T) ≫
        stableFiberConnecting (Fibration.changeWeakPrespectrumMap (perfectOpenNested j)) d =
      stableFiberConnecting
        (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T)) d ≫
          (stableHomotopyFunctor d).map (perfectSupportedOpenForgetFiberPrespectrumMap j T) :=
  perfectSupportedOpenForgetFiberPrespectrumMap_connecting j T d

example (n : ℕ)
    (a : PerfectSupportedOpenCoarseK j T n) :
    originalKStableEquiv (perfectOpenWeakWaldhausen j) n
        (Additive.ofMul (perfectSupportedOpenKForget j T n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (perfectSupportedOpenForgetPrespectrumMap j T)
        (originalKStableEquiv (perfectSupportedOpenWeakWaldhausen j T) n (Additive.ofMul a)) :=
  perfectSupportedOpenForgetPrespectrumMap_naturality j T n a

example (n : ℕ)
    (a : PerfectSupportedK (T ⊔ j.opensRange).ι n) :
    originalKStableEquiv (perfectSupportedWaldhausen j) n
        (Additive.ofMul (perfectSupportedUnionForgetKMap j T n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (perfectSupportedUnionForgetPrespectrumMap j T)
        (originalKStableEquiv (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι) n
          (Additive.ofMul a)) :=
  perfectSupportedUnionForgetPrespectrumMap_naturality j T n a

example :
    perfectSupportedUnionToAcyclicPrespectrumMap j T ≫
        originalPrespectrumMap
          (Fibration.acyclicStructure (perfectSupportedOpenNested j T))
          (Fibration.acyclicStructure (perfectOpenNested j))
          (Fibration.acyclicFunctor_exact (perfectSupportedOpenNested j T) (perfectOpenNested j)
            (perfectSupportedInclusion_isExact T.ι)
            (perfectSupportedInclusion_open_isExact j T)) rfl =
      perfectSupportedUnionForgetPrespectrumMap j T ≫
        perfectSupportedToAcyclicPrespectrumMap j :=
  perfectSupportedUnionForgetPrespectrumMap_toAcyclic j T

example (n : ℕ) (s : unitInterval)
    (x : (perfectSupportedUnionPrespectrum j T).space n) :
    (perfectSupportedOpenForgetPrespectrumMap j T).map n
        ((perfectSupportedUnionPrespectrumNullhomotopy j T).level n (s, x)) =
      (perfectSupportedPrespectrumNullhomotopy j).level n
        (s, (perfectSupportedUnionForgetPrespectrumMap j T).map n x) :=
  perfectSupportedUnionPrespectrumNullhomotopy_forget j T n s x

example (n : ℕ)
    (s t : unitInterval) (x : (perfectSupportedUnionPrespectrum j T).space n) :
    (perfectSupportedOpenForgetPrespectrumMap j T).map (n + 1)
        ((perfectSupportedUnionPrespectrumNullhomotopy j T).level (n + 1)
          (s, (perfectSupportedUnionPrespectrum j T).structureMap n x t)) =
      (perfectOpenPrespectrum j).structureMap n
        ((perfectSupportedPrespectrumNullhomotopy j).level n
          (s, (perfectSupportedUnionForgetPrespectrumMap j T).map n x)) t :=
  perfectSupportedUnionPrespectrumNullhomotopy_forget_structure j T n s t x

example :
    perfectSupportedUnionFiberPrespectrumMap j T ≫
        perfectSupportedOpenForgetFiberPrespectrumMap j T =
      perfectSupportedUnionForgetPrespectrumMap j T ≫
        perfectSupportedFiberPrespectrumMap j :=
  perfectSupportedUnionFiberPrespectrumMap_forget j T

example : LoopPrespectrum.Homotopy
    (perfectSupportedUnionFiberPrespectrumRebasedMap j T ≫
      perfectSupportedOpenForgetFiberPrespectrumMap j T)
    (perfectSupportedUnionForgetPrespectrumMap j T ≫
      perfectSupportedFiberPrespectrumRebasedMap j) :=
  perfectSupportedUnionFiberPrespectrumRebasedForgetHomotopy j T

example :
    (perfectOpenWeakWaldhausen j).asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun.comp
        (deloopingMap (perfectSupportedInclusion_open_isExact j T)).hom =
      ((perfectSupportedOpenForgetPrespectrumMap j T).map 1).comp
        (perfectSupportedOpenWeakWaldhausen j T).asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun :=
  perfectSupportedOpenForgetPrespectrumMap_level_one_square j T

example :
    (perfectSupportedWaldhausen j).asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun.comp
        (deloopingMap (perfectSupportedUnionForget_isExact j T)).hom =
      ((perfectSupportedUnionForgetPrespectrumMap j T).map 1).comp
        (perfectSupportedWaldhausen
          (T ⊔ j.opensRange).ι).asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun :=
  perfectSupportedUnionForgetPrespectrumMap_level_one_square j T

example (d : ℤ) :
    perfectSupportedOpenStableConnecting j T d ≫
        (stableHomotopyFunctor d).map (perfectSupportedUnionForgetPrespectrumMap j T) =
      (stableHomotopyFunctor (d + 1)).map (perfectSupportedOpenForgetPrespectrumMap j T) ≫
        perfectOpenStableConnecting j d :=
  perfectSupportedOpenStableConnecting_forget j T d

example (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (a : PerfectSupportedOpenCoarseK j T (n + 1)) :
    stableFiberConnecting
        (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T)) (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup (perfectSupportedOpenPrespectrum j T)) κ)
          (originalKStableEquiv (perfectSupportedOpenWeakWaldhausen j T) (n + 1)
            (Additive.ofMul a))) =
      -((stableHomotopyFunctor (n : ℤ)).map (perfectSupportedUnionFiberPrespectrumMap j T)
        (originalKStableEquiv (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι) n
          (Additive.ofMul (perfectSupportedOpenConnectingHom j T n a)))) :=
  perfectSupportedUnionFiberPrespectrumMap_connecting_sign j T n κ a

example (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1) (a : PerfectOpenK j (n + 1)) :
    stableFiberConnecting (Fibration.changeWeakPrespectrumMap (perfectOpenNested j)) (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup (perfectOpenPrespectrum j)) κ)
          (originalKStableEquiv (perfectOpenWeakWaldhausen j) (n + 1) (Additive.ofMul a))) =
      -((stableHomotopyFunctor (n : ℤ)).map (perfectSupportedFiberPrespectrumMap j)
        (originalKStableEquiv (perfectSupportedWaldhausen j) n
          (Additive.ofMul (perfectOpenConnectingHom j n a)))) :=
  perfectSupportedFiberPrespectrumMap_connecting_sign j n κ a

example (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (a : PerfectSupportedOpenCoarseK j T (n + 1)) :
    perfectSupportedOpenStableConnecting j T (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup (perfectSupportedOpenPrespectrum j T)) κ)
          (originalKStableEquiv (perfectSupportedOpenWeakWaldhausen j T) (n + 1)
            (Additive.ofMul a))) =
      -(originalKStableEquiv (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι) n
        (Additive.ofMul (perfectSupportedOpenConnectingHom j T n a))) :=
  perfectSupportedOpenStableConnecting_sign j T n κ a

example (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1) (a : PerfectOpenK j (n + 1)) :
    perfectOpenStableConnecting j (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup (perfectOpenPrespectrum j)) κ)
          (originalKStableEquiv (perfectOpenWeakWaldhausen j) (n + 1) (Additive.ofMul a))) =
      -(originalKStableEquiv (perfectSupportedWaldhausen j) n
        (Additive.ofMul (perfectOpenConnectingHom j n a))) :=
  perfectOpenStableConnecting_sign j n κ a

-- At degree zero the actual boundary is K₁ to K₀, with its negative stable sign.
example (a : PerfectSupportedOpenCoarseK j T 1) :
    perfectSupportedOpenStableConnecting j T 0
        (originalKStableEquiv (perfectSupportedOpenWeakWaldhausen j T) 1
          (Additive.ofMul a)) =
      -(originalKStableEquiv (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι) 0
        (Additive.ofMul (perfectSupportedOpenConnectingHom j T 0 a))) :=
  perfectSupportedOpenStableConnecting_sign j T 0 rfl a

example :
    perfectSupportedOpenStableConnecting j T 0 ≫
        (stableHomotopyFunctor 0).map (perfectSupportedUnionForgetPrespectrumMap j T) =
      (stableHomotopyFunctor 1).map (perfectSupportedOpenForgetPrespectrumMap j T) ≫
        perfectOpenStableConnecting j 0 :=
  perfectSupportedOpenStableConnecting_forget j T 0

example :
    (perfectSupportedUnionForgetKMap j T 0).comp
        (perfectSupportedOpenConnectingHom j T 0 : PerfectSupportedOpenCoarseK j T 1 →*
          PerfectSupportedK (T ⊔ j.opensRange).ι 0) =
      (perfectOpenConnectingHom j 0 : PerfectOpenK j 1 →* PerfectSupportedK j 0).comp
        (perfectSupportedOpenKForget j T 1) :=
  perfectSupportedOpenConnectingHom_forget j T 0

-- The restriction homotopy is based and respects independent homotopy/structure times.
example (n : ℕ) (s t : unitInterval)
    (x : (perfectSupportedOpenPrespectrum j T).space n) :
    (perfectSupportedOpenForgetPrespectrumRestrictHomotopy j T).level (n + 1)
        (s, (perfectSupportedOpenPrespectrum j T).structureMap n x t) =
      (originalPrespectrum
        (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)).structureMap n
        ((perfectSupportedOpenForgetPrespectrumRestrictHomotopy j T).level n (s, x)) t :=
  (perfectSupportedOpenForgetPrespectrumRestrictHomotopy j T).comm n s x t

-- The chosen-zero and rebased presentations retain the entire level-one fiber path.
example :
    (Fibration.originalFiberToSpectrumLevelOne (perfectSupportedOpenNested j
      T)).toHomotopyEquiv.toFun.comp (perfectSupportedUnionFiberMap j T) =
      ((perfectSupportedUnionFiberPrespectrumMap j T).map 1).comp
        (perfectSupportedWaldhausen (T ⊔
          j.opensRange).ι).asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun :=
  perfectSupportedUnionFiberPrespectrumMap_level_one_square j T

example (n : ℕ) :
    HomotopyGroup.piMap n (perfectSupportedUnionFiberMap j T)
      (perfectSupportedUnionFiberMap_basepoint j T) = perfectSupportedUnionFiberKMap j T n :=
  perfectSupportedUnionFiberMap_piMap j T n

-- Level zero is the actual loop-stage construction, with independent null and structure times.
example (s : unitInterval) (x : (perfectSupportedUnionPrespectrum j T).space 0) :
    (perfectSupportedOpenForgetPrespectrumMap j T).map 0
        ((perfectSupportedUnionPrespectrumNullhomotopy j T).level 0 (s, x)) =
      (perfectSupportedPrespectrumNullhomotopy j).level 0
        (s, (perfectSupportedUnionForgetPrespectrumMap j T).map 0 x) :=
  perfectSupportedUnionPrespectrumNullhomotopy_forget j T 0 s x

example (s t : unitInterval) (x : (perfectSupportedUnionPrespectrum j T).space 0) :
    (perfectSupportedOpenForgetPrespectrumMap j T).map 1
        ((perfectSupportedUnionPrespectrumNullhomotopy j T).level 1
          (s, (perfectSupportedUnionPrespectrum j T).structureMap 0 x t)) =
      (perfectOpenPrespectrum j).structureMap 0
        ((perfectSupportedPrespectrumNullhomotopy j).level 0
          (s, (perfectSupportedUnionForgetPrespectrumMap j T).map 0 x)) t :=
  perfectSupportedUnionPrespectrumNullhomotopy_forget_structure j T 0 s t x

section Generic

open Fibration

universe v

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D}
  (N : NestedWeakEquivalences V) (M : NestedWeakEquivalences W)
  {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hFc : IsExact N.coarse.cof N.coarse.weq M.coarse.cof M.coarse.weq F)

example (h0 : F.obj V.zero = W.zero) :
    changeWeakPrespectrumMap N ≫
        originalPrespectrumMap N.coarse M.coarse hFc (coarse_zero_eq N M h0) =
      originalPrespectrumMap V W hF h0 ≫ changeWeakPrespectrumMap M :=
  changeWeakPrespectrumMap_natural N M hF hFc h0

example (h0 : F.obj V.zero = W.zero) :
    acyclicInclusionPrespectrumMap N ≫ originalPrespectrumMap V W hF h0 =
      originalPrespectrumMap (acyclicStructure N) (acyclicStructure M)
        (acyclicFunctor_exact N M hF hFc) (acyclicFunctor_zero N M hFc h0) ≫
        acyclicInclusionPrespectrumMap M :=
  acyclicInclusionPrespectrumMap_natural N M hF hFc h0

example (h0 : F.obj V.zero = W.zero)
    (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (acyclicStructure N)).space n) :
    (originalPrespectrumMap N.coarse M.coarse hFc (coarse_zero_eq N M h0)).map n
        ((acyclicPrespectrumNullhomotopy N).level n (s, x)) =
      (acyclicPrespectrumNullhomotopy M).level n
        (s, (originalPrespectrumMap (acyclicStructure N) (acyclicStructure M)
          (acyclicFunctor_exact N M hF hFc) (acyclicFunctor_zero N M hFc h0)).map n x) :=
  acyclicPrespectrumNullhomotopy_natural N M hF hFc h0 n s x

example (h0 : F.obj V.zero = W.zero)
    (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (acyclicStructure N)).space n) :
    (originalPrespectrumMap N.coarse M.coarse hFc (coarse_zero_eq N M h0)).map (n + 1)
        ((acyclicPrespectrumNullhomotopy N).level (n + 1)
          (s, (originalPrespectrum (acyclicStructure N)).structureMap n x t)) =
      (originalPrespectrum M.coarse).structureMap n
        ((acyclicPrespectrumNullhomotopy M).level n
          (s, (originalPrespectrumMap (acyclicStructure N) (acyclicStructure M)
            (acyclicFunctor_exact N M hF hFc) (acyclicFunctor_zero N M hFc h0)).map n x)) t :=
  acyclicPrespectrumNullhomotopy_natural_structure N M hF hFc h0 n s t x

example (h0 : F.obj V.zero = W.zero) :
    canonicalFiberPrespectrumMap N ≫ fiberFunctorPrespectrumMap N M hF hFc h0 =
      originalPrespectrumMap (acyclicStructure N) (acyclicStructure M)
        (acyclicFunctor_exact N M hF hFc) (acyclicFunctor_zero N M hFc h0) ≫
        canonicalFiberPrespectrumMap M :=
  canonicalFiberPrespectrumMap_natural N M hF hFc h0

example (h0 : F.obj V.zero = W.zero) (d : ℤ) :
    (LoopPrespectrum.stableHomotopyFunctor (d + 1)).map
        (originalPrespectrumMap N.coarse M.coarse hFc (coarse_zero_eq N M h0)) ≫
        LoopPrespectrum.stableFiberConnecting (changeWeakPrespectrumMap M) d =
      LoopPrespectrum.stableFiberConnecting (changeWeakPrespectrumMap N) d ≫
        (LoopPrespectrum.stableHomotopyFunctor d).map
          (fiberFunctorPrespectrumMap N M hF hFc h0) :=
  stableFiberConnecting_natural N M hF hFc h0 d

end Generic
