/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedUnionPrespectrum
public import Colib.KTheory.Waldhausen.Iterated.ExactCoherence
public import Colib.KTheory.Waldhausen.Iterated.StableFunctoriality

/-!
# Actual supported restriction and its coarse factorization

The original change-of-weak-equivalences map followed by supported restriction is
coherently homotopic to the actual exact supported restriction. Canonical zero rebasing
is retained, rather than asserting strict composition of rebased functors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology Topology.LoopPrespectrum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- Actual supported restriction from the coarse model, with canonical zero rebasing. -/
def perfectSupportedOpenRestrictPrespectrumMap : perfectSupportedOpenPrespectrum j T ⟶
    originalPrespectrum (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) :=
  exactOriginalPrespectrumMap (perfectSupportedOpenWeakWaldhausen j T)
    (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι)
    (perfectSupportedOpenRestrict_waldhausenExact j T)

/-- Actual fine supported open restriction, retaining its original exact functor. -/
def perfectSupportedRestrictPrespectrumMap :
    originalPrespectrum (perfectSupportedWaldhausen T.ι) ⟶
      originalPrespectrum (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) :=
  exactOriginalPrespectrumMap (perfectSupportedWaldhausen T.ι)
    (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) (perfectSupportedRestrict_exact j T)

/-- Normalization and exact composition give the whole actual restriction factorization. -/
def perfectSupportedOpenRestrictionHomotopy : Homotopy
    (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T) ≫
      perfectSupportedOpenRestrictPrespectrumMap j T)
    (perfectSupportedRestrictPrespectrumMap j T) := by
  have H := (exactOriginalPrespectrumMapChosenZeroHomotopy
    (perfectSupportedWaldhausen T.ι) (perfectSupportedOpenWeakWaldhausen j T)
    (Fibration.changeWeak_exact (perfectSupportedOpenNested j T)) rfl).symm.postcomp
      (perfectSupportedOpenRestrictPrespectrumMap j T)
  exact H.trans (exactOriginalPrespectrumMapCompHomotopy
    (perfectSupportedWaldhausen T.ι) (perfectSupportedOpenWeakWaldhausen j T)
    (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι)
    (Fibration.changeWeak_exact (perfectSupportedOpenNested j T))
    (perfectSupportedOpenRestrict_waldhausenExact j T)).symm

/-- The factorization retains the actual maps in every integer stable degree. -/
theorem perfectSupportedOpenRestrictPrespectrumMap_comp_stable (k : ℤ) :
    (stableHomotopyFunctor k).map
        (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T)) ≫
      (stableHomotopyFunctor k).map (perfectSupportedOpenRestrictPrespectrumMap j T) =
        (stableHomotopyFunctor k).map (perfectSupportedRestrictPrespectrumMap j T) := by
  rw [← Functor.map_comp]
  exact (perfectSupportedOpenRestrictionHomotopy j T).stableHomotopyMap_eq k

/-- Coarse restriction retains its existing K-map in every connective degree. -/
theorem perfectSupportedOpenRestrictPrespectrumMap_naturality (n : ℕ)
    (a : PerfectSupportedOpenCoarseK j T n) :
    originalKStableEquiv (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) n
        (Additive.ofMul (perfectSupportedOpenKRestrict j T n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (perfectSupportedOpenRestrictPrespectrumMap j T)
        (originalKStableEquiv (perfectSupportedOpenWeakWaldhausen j T) n (Additive.ofMul a)) :=
  originalKStableEquiv_exact_naturality _ _
    (perfectSupportedOpenRestrict_waldhausenExact j T) n a

/-- Fine restriction also retains the actual supported K-map. -/
theorem perfectSupportedRestrictPrespectrumMap_naturality (n : ℕ)
    (a : PerfectSupportedK T.ι n) :
    originalKStableEquiv (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) n
        (Additive.ofMul (perfectSupportedKRestrict j T n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (perfectSupportedRestrictPrespectrumMap j T)
        (originalKStableEquiv (perfectSupportedWaldhausen T.ι) n (Additive.ofMul a)) :=
  originalKStableEquiv_exact_naturality _ _ (perfectSupportedRestrict_exact j T) n a

/-- The actual coarse model is an Omega prespectrum. -/
theorem perfectSupportedOpenPrespectrum_isOmega : IsOmega (perfectSupportedOpenPrespectrum j T) :=
  originalPrespectrum_isOmega (perfectSupportedOpenWeakWaldhausen j T)

/-- Its actual stable groups vanish in every negative integer degree. -/
theorem perfectSupportedOpenPrespectrum_neg_subsingleton (k : ℤ) (hk : k < 0) :
    Subsingleton (stableHomotopyGroup (perfectSupportedOpenPrespectrum j T) k) :=
  originalStableHomotopyGroup_neg_subsingleton (perfectSupportedOpenWeakWaldhausen j T) k hk

attribute [colib_tag "COL-0335"]
  perfectSupportedOpenRestrictionHomotopy
  perfectSupportedOpenRestrictPrespectrumMap_comp_stable
  perfectSupportedOpenRestrictPrespectrumMap_naturality
  perfectSupportedRestrictPrespectrumMap_naturality

end AlgebraicGeometry.Scheme.Modules
