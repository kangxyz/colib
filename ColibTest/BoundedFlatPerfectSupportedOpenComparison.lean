/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedOpenComparison

/-! Actual objects, quotient, restriction, K-zero and whole-track consumers. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Fibration CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open Topology Topology.LoopPrespectrum

universe u
attribute [local instance] Abelian.hasFiniteBiproducts

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

example {K L : (boundedAboveFlatPerfectSupported T.ι).FullSubcategory} (f : K ⟶ L) :
    (boundedAboveFlatPerfectSupportedOpenWaldhausen j T).weq f ↔
      QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom) :=
  boundedAboveFlatPerfectSupportedOpenWaldhausen_weq_iff j T f

example {K L : (boundedAboveFlatPerfectSupported T.ι).FullSubcategory} (f : K ⟶ L) :
    (boundedAboveFlatPerfectSupportedOpenWaldhausen j T).cof f ↔
      ∃ (Q : CochainComplex X.Modules ℤ) (_hQ : boundedAboveFlatPerfectSupported T.ι Q)
        (p : L.obj ⟶ Q) (h : f.hom ≫ p = 0),
        (ShortComplex.mk f.hom p h).ShortExact :=
  boundedAboveFlatPerfectSupportedOpenWaldhausen_cof_iff j T f

example [CompactSpace X]
    (K : (boundedAboveFlatPerfectSupported T.ι).FullSubcategory)
    (L : (perfectSupported T.ι).FullSubcategory)
    (f : (boundedAboveFlatPerfectSupportedInclusion T.ι).obj K ⟶ L) :
    ∃ (M : (boundedAboveFlatPerfectSupported T.ι).FullSubcategory) (i : K ⟶ M)
      (p : (boundedAboveFlatPerfectSupportedInclusion T.ι).obj M ⟶ L)
      (Q : CochainComplex X.Modules ℤ) (_hQ : boundedAboveFlatPerfectSupported T.ι Q)
      (q : M.obj ⟶ Q) (w : i.hom ≫ q = 0),
      (ShortComplex.mk i.hom q w).ShortExact ∧
        QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map p.hom) ∧
        (boundedAboveFlatPerfectSupportedInclusion T.ι).map i ≫ p = f := by
  obtain ⟨M, i, p, hi, hp, hfac⟩ :=
    (boundedAboveFlatPerfectSupportedOpenInclusion_approximation j T).lift f
  obtain ⟨Q, hQ, q, w, hS⟩ :=
    (boundedAboveFlatPerfectSupportedOpenWaldhausen_cof_iff j T i).1 hi
  exact ⟨M, i, p, Q, hQ, q, w, hS, hp, hfac⟩

example [CompactSpace X] (n : ℕ) :
    Function.Bijective (KMap (boundedAboveFlatPerfectSupportedOpenInclusion_isExact j T) n) :=
  boundedAboveFlatPerfectSupportedOpenToPerfectKMap_bijective j T n

example [CompactSpace X] :
    (↑(boundedAboveFlatPerfectSupportedOpenKEquiv j T 0) :
      BoundedAboveFlatPerfectSupportedOpenK j T 0 →* PerfectSupportedOpenCoarseK j T 0) =
        KMap (boundedAboveFlatPerfectSupportedOpenInclusion_isExact j T) 0 := rfl

example [CompactSpace X] (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map
      (boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap j T)) :=
  boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap_isStableEquivalence j T d

example [CompactSpace X] :
    IsIso ((stableHomotopyFunctor (-1)).map
      (boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap j T)) :=
  boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap_isStableEquivalence j T (-1)

example [CompactSpace X] :
    IsIso ((stableHomotopyFunctor 0).map
      (boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap j T)) :=
  boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap_isStableEquivalence j T 0

example (a : BoundedAboveFlatPerfectSupportedOpenK j T 0) :
    originalKStableEquiv (perfectSupportedOpenWeakWaldhausen j T) 0
        (Additive.ofMul (boundedAboveFlatPerfectSupportedOpenToPerfectKMap j T 0 a)) =
      (stableHomotopyFunctor 0).map
        (boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap j T)
        (originalKStableEquiv (boundedAboveFlatPerfectSupportedOpenWaldhausen j T) 0
          (Additive.ofMul a)) :=
  boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap_originalK_naturality j T 0 a

example (n : ℕ) :
    (boundedAboveFlatPerfectSupportedOpenToPerfectKMap j T n).comp
        (boundedAboveFlatPerfectSupportedOpenKMap j T n) =
      (perfectSupportedOpenKMap j T n).comp
        (boundedAboveFlatPerfectSupportedToPerfectKMap T.ι n) :=
  boundedAboveFlatPerfectSupportedOpenToPerfectKMap_changeWeak j T n

example (n : ℕ) (x : (originalPrespectrum
    (boundedAboveFlatPerfectSupportedWaldhausen T.ι)).space n) :
    (boundedAboveFlatPerfectSupportedOpenChangeWeakHomotopy j T).level n (0, x) =
      (changeWeakPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j T) ≫
        boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap j T).map n x :=
  (boundedAboveFlatPerfectSupportedOpenChangeWeakHomotopy j T).at_zero n x

example (n : ℕ) (x : (originalPrespectrum
    (boundedAboveFlatPerfectSupportedWaldhausen T.ι)).space n) :
    (boundedAboveFlatPerfectSupportedOpenChangeWeakHomotopy j T).level n (1, x) =
      (boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap T.ι ≫
        changeWeakPrespectrumMap (perfectSupportedOpenNested j T)).map n x :=
  (boundedAboveFlatPerfectSupportedOpenChangeWeakHomotopy j T).at_one n x

example (n : ℕ) (s t : unitInterval) (x : (originalPrespectrum
    (boundedAboveFlatPerfectSupportedWaldhausen T.ι)).space n) :
    (boundedAboveFlatPerfectSupportedOpenChangeWeakHomotopy j T).level (n + 1)
        (s, (originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen T.ι)).structureMap
          n x t) =
      (perfectSupportedOpenPrespectrum j T).structureMap n
        ((boundedAboveFlatPerfectSupportedOpenChangeWeakHomotopy j T).level n (s, x)) t :=
  (boundedAboveFlatPerfectSupportedOpenChangeWeakHomotopy j T).comm n s x t

example (d : ℤ) :
    (stableHomotopyFunctor d).map
        (changeWeakPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j T) ≫
          boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap j T) =
      (stableHomotopyFunctor d).map
        (boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap T.ι ≫
          changeWeakPrespectrumMap (perfectSupportedOpenNested j T)) :=
  boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap_changeWeak_stable j T d
