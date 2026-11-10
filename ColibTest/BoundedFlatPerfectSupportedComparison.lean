/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedComparison
import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedEvaluationSpectrum

/-! Full-signature consumers for supported approximation and the actual inclusion maps. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.Fibration
open AlgebraicGeometry AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Modules
open Topology Topology.LoopPrespectrum
universe u
attribute [local instance] Abelian.hasFiniteBiproducts

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

example (K : (boundedAboveFlatPerfectSupported j).FullSubcategory) :
    ((boundedAboveFlatPerfectSupportedInclusion j).obj K).obj = K.obj := rfl

example {K L : CochainComplex X.Modules ℤ}
    (hK : boundedAboveFlatPerfectSupported j K) (hL : boundedAboveFlatPerfectSupported j L)
    (f : K ⟶ L) : boundedAboveFlatPerfectSupported j (CochainComplex.mappingCone f) :=
  boundedAboveFlatPerfectSupported_mappingCone j hK hL f

example {K : CochainComplex X.Modules ℤ} (hK : boundedAboveFlatPerfectSupported j K) :
    boundedAboveFlatPerfectSupported j (K⟦(1 : ℤ)⟧) :=
  boundedAboveFlatPerfectSupported_shift_one j hK

example : RowFactorization.JointData
    (NestedWeakEquivalences.refl (boundedAboveFlatPerfectSupportedWaldhausen j)) :=
  boundedAboveFlatPerfectSupportedJointData j

example [CompactSpace X]
    (K : (boundedAboveFlatPerfectSupported j).FullSubcategory)
    (L : (perfectSupported j).FullSubcategory)
    (f : (boundedAboveFlatPerfectSupportedInclusion j).obj K ⟶ L) :
    ∃ (M : (boundedAboveFlatPerfectSupported j).FullSubcategory) (i : K ⟶ M)
      (p : (boundedAboveFlatPerfectSupportedInclusion j).obj M ⟶ L)
      (Q : CochainComplex X.Modules ℤ) (_hQ : boundedAboveFlatPerfectSupported j Q)
      (q : M.obj ⟶ Q) (w : i.hom ≫ q = 0),
      (ShortComplex.mk i.hom q w).ShortExact ∧ QuasiIso p.hom ∧
        (boundedAboveFlatPerfectSupportedInclusion j).map i ≫ p = f := by
  obtain ⟨M, i, p, hi, hp, hfac⟩ :=
    (boundedAboveFlatPerfectSupportedInclusion_approximation j).lift f
  obtain ⟨Q, hQ, q, w, hS⟩ :=
    (boundedAboveFlatPerfectSupportedWaldhausen_cof_iff j i).1 hi
  exact ⟨M, i, p, Q, hQ, q, w, hS, hp, hfac⟩

example [CompactSpace X] (n : ℕ) :
    Function.Bijective (KMap (boundedAboveFlatPerfectSupportedInclusion_isExact j) n) :=
  boundedAboveFlatPerfectSupportedToPerfectKMap_bijective j n

example [CompactSpace X] :
    (↑(boundedAboveFlatPerfectSupportedKEquiv j 0) :
      BoundedAboveFlatPerfectSupportedK j 0 →* PerfectSupportedK j 0) =
        KMap (boundedAboveFlatPerfectSupportedInclusion_isExact j) 0 := rfl

example (n : ℕ) :
    (perfectSupportedKMap j n).comp (boundedAboveFlatPerfectSupportedToPerfectKMap j n) =
      (boundedAboveFlatPerfectToPerfectKMap X.toRingedSpace n).comp
        (boundedAboveFlatPerfectSupportedForgetKMap j n) :=
  boundedAboveFlatPerfectSupportedToPerfectKMap_forget j n

example [CompactSpace X] (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map
      (boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap j)) :=
  boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap_isStableEquivalence j d

example [CompactSpace X] :
    IsIso ((stableHomotopyFunctor (-1)).map
      (boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap j)) :=
  boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap_isStableEquivalence j (-1)

example [CompactSpace X] :
    IsIso ((stableHomotopyFunctor 0).map
      (boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap j)) :=
  boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap_isStableEquivalence j 0

example (n : ℕ) (a : BoundedAboveFlatPerfectSupportedK j n) :
    originalKStableEquiv (perfectSupportedWaldhausen j) n
        (Additive.ofMul (boundedAboveFlatPerfectSupportedToPerfectKMap j n a)) =
      (stableHomotopyFunctor (n : ℤ)).map
        (boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap j)
        (originalKStableEquiv (boundedAboveFlatPerfectSupportedWaldhausen j) n
          (Additive.ofMul a)) :=
  boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap_originalK_naturality j n a

example (a : BoundedAboveFlatPerfectSupportedK j 0) :
    originalZeroSpaceEquiv (perfectSupportedWaldhausen j) 0
        (boundedAboveFlatPerfectSupportedToPerfectKMap j 0 a) =
      HomotopyGroup.map ((boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap j).map 0)
        ((boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap j).map_point 0)
        (originalZeroSpaceEquiv (boundedAboveFlatPerfectSupportedWaldhausen j) 0 a) :=
  boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap_zeroSpace_naturality j 0 a

example (n : ℕ) (x : (originalPrespectrum
    (boundedAboveFlatPerfectSupportedWaldhausen j)).space n) :
    (boundedAboveFlatPerfectSupportedToPerfectPrespectrumForgetHomotopy j).level n (0, x) =
      (boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap j ≫
        perfectSupportedInclusionPrespectrumMap j).map n x :=
  (boundedAboveFlatPerfectSupportedToPerfectPrespectrumForgetHomotopy j).at_zero n x

example (n : ℕ) (x : (originalPrespectrum
    (boundedAboveFlatPerfectSupportedWaldhausen j)).space n) :
    (boundedAboveFlatPerfectSupportedToPerfectPrespectrumForgetHomotopy j).level n (1, x) =
      (boundedAboveFlatPerfectSupportedForgetPrespectrumMap j ≫
        boundedAboveFlatPerfectToPerfectPrespectrumMap X.toRingedSpace).map n x :=
  (boundedAboveFlatPerfectSupportedToPerfectPrespectrumForgetHomotopy j).at_one n x

example (n : ℕ) (s t : unitInterval) (x : (originalPrespectrum
    (boundedAboveFlatPerfectSupportedWaldhausen j)).space n) :
    (boundedAboveFlatPerfectSupportedToPerfectPrespectrumForgetHomotopy j).level (n + 1)
        (s, (originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j)).structureMap
          n x t) =
      (originalPrespectrum (perfectComplexesWaldhausen X.toRingedSpace)).structureMap n
        ((boundedAboveFlatPerfectSupportedToPerfectPrespectrumForgetHomotopy j).level n (s, x))
        t :=
  (boundedAboveFlatPerfectSupportedToPerfectPrespectrumForgetHomotopy j).comm n s x t

example (d : ℤ) :
    (stableHomotopyFunctor d).map
        (boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap j ≫
          perfectSupportedInclusionPrespectrumMap j) =
      (stableHomotopyFunctor d).map
        (boundedAboveFlatPerfectSupportedForgetPrespectrumMap j ≫
          boundedAboveFlatPerfectToPerfectPrespectrumMap X.toRingedSpace) :=
  boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap_forget_stable j d

-- The actual frozen evaluation lands stably in the native perfect model.
example {R : CommRingCat.{u}} {V : Scheme.{u}}
    (j : V ⟶ Scheme.Spec.obj (Opposite.op R)) [IsOpenImmersion j] :
    IsStableEquivalence (boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap j ≫
      boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap j) :=
  IsStableEquivalence.comp (boundedAboveFlatAffineSupportedSectionEvaluation_isStableEquivalence j)
    (boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap_isStableEquivalence j)
