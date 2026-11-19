/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassLocalizedSpectrum
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassStableColimit
public import Colib.AlgebraicGeometry.KTheory.PerfectPullbackCompatibility

/-!
# Consumers of the initial affine perfect spectrum map

The two comparison inverses, actual Laurent seed, negative colimit leg, coefficient
composition and original perfect K-zero law are checked on the native definitions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace ColibTest.AlgebraicGeometry.AffineBassLocalizedSpectrum

/-- Bounded-above-flat inputs use the actual prespectrum evaluation inverse and initial face. -/
theorem boundedAboveFlat_representative (R : CommRingCat.{u}) :
    (boundedAboveFlatPerfectSpectrumIso (Spec R)).hom ≫ affinePerfectBassTelescopeInitialMap R =
      toStableLocalization.map (boundedAboveFlatAffineEvaluationInversePrespectrumMap R ≫
        boundedAboveFlatAffineSectionBassTelescopeInitial.app R) := by
  rw [affinePerfectBassTelescopeInitialMap_eq, Iso.hom_inv_id_assoc]

/-- The first actual cylinder transports the initial map across the unchanged Laurent seed. -/
theorem seed_first_stage (R : CommRingCat.{u}) :
    affinePerfectBassTelescopeInitialMap R =
      (boundedAboveFlatPerfectSpectrumIso (Spec R)).inv ≫
        toStableLocalization.map (boundedAboveFlatAffineEvaluationInversePrespectrumMap R ≫
          boundedAboveFlatAffineSectionBassSeed.app R ≫
            (boundedAboveFlatAffineSectionBassTelescopeInclusion 1).app R) := by
  rw [affinePerfectBassTelescopeInitialMap_eq]
  apply congrArg (fun a ↦ (boundedAboveFlatPerfectSpectrumIso (Spec R)).inv ≫ a)
  have h := toStableLocalization_map_eq_of_homotopy
    (Homotopy.precomp (boundedAboveFlatAffineEvaluationInversePrespectrumMap R)
      (boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy R 0))
  change toStableLocalization.map (boundedAboveFlatAffineEvaluationInversePrespectrumMap R ≫
      (boundedAboveFlatAffineSectionBassTelescopeInclusion 0).app R) = _
  simpa only [boundedAboveFlatAffineSectionBassTransition_zero, Nat.zero_add] using h

/-- The signed initial map goes to the actual stage-zero colimit leg, including negative degrees. -/
theorem initial_colimit_leg (R : CommRingCat.{u}) (d : ℤ) :
    (localizedStableHomotopyFunctor d).map (affinePerfectBassTelescopeInitialMap R) ≫
        (boundedAboveFlatAffineSectionBassStableColimitIso R d).inv =
      (localizedStableHomotopyFunctor d).map (boundedAboveFlatPerfectSpectrumIso (Spec R)).inv ≫
        (stableHomotopyFunctor d).map
          (boundedAboveFlatAffineEvaluationInversePrespectrumMap R) ≫
        colimit.ι (boundedAboveFlatAffineSectionBassStableDiagram R d) 0 := by
  have h := congrArg (fun f ↦ f ≫ (boundedAboveFlatAffineSectionBassStableColimitIso R d).inv)
    (boundedAboveFlatAffineSectionBassStableColimitIso_ι_hom R d 0)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  change colimit.ι (boundedAboveFlatAffineSectionBassStableDiagram R d) 0 =
    (stableHomotopyFunctor d).map (boundedAboveFlatAffineSectionBassTelescopeInitial.app R) ≫
      (boundedAboveFlatAffineSectionBassStableColimitIso R d).inv at h
  rw [affinePerfectBassTelescopeInitialMap_stable]
  simp only [Category.assoc, ← h]

/-- Two successive derived coefficient pullbacks commute with the initial map. -/
theorem two_coefficient_initial {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    perfectLocalizedPullback (Spec.map f) ≫ perfectLocalizedPullback (Spec.map g) ≫
        affinePerfectBassTelescopeInitialMap T =
      affinePerfectBassTelescopeInitialMap R ≫
        toStableLocalization.map (boundedAboveFlatAffineSectionBassTelescopeMap f) ≫
        toStableLocalization.map (boundedAboveFlatAffineSectionBassTelescopeMap g) := by
  have h := affinePerfectBassTelescopeInitialMap_naturality (f ≫ g)
  rw [Spec.map_comp, perfectLocalizedPullback_comp,
    boundedAboveFlatAffineSectionBassTelescopeMap_comp, Functor.map_comp] at h
  simpa only [Category.assoc] using h

/-- The induced map at degree zero preserves the original perfect K-zero group law. -/
theorem original_KZero_addition (R : CommRingCat.{u})
    (a b : (perfectComplexesWaldhausen (Spec R).toRingedSpace).K 0) :
    (localizedStableHomotopyFunctor 0).map (affinePerfectBassTelescopeInitialMap R)
        (originalKStableEquiv (perfectComplexesWaldhausen (Spec R).toRingedSpace) 0
          (Additive.ofMul (a * b))) =
      (localizedStableHomotopyFunctor 0).map (affinePerfectBassTelescopeInitialMap R)
          (originalKStableEquiv (perfectComplexesWaldhausen (Spec R).toRingedSpace) 0
            (Additive.ofMul a)) +
        (localizedStableHomotopyFunctor 0).map (affinePerfectBassTelescopeInitialMap R)
          (originalKStableEquiv (perfectComplexesWaldhausen (Spec R).toRingedSpace) 0
            (Additive.ofMul b)) := by
  change (localizedStableHomotopyFunctor 0).map (affinePerfectBassTelescopeInitialMap R)
    (originalKStableEquiv (perfectComplexesWaldhausen (Spec R).toRingedSpace) 0
      (Additive.ofMul a + Additive.ofMul b)) = _
  rw [map_add, map_add]

/-- For flat coefficients the initial map retains the original flat exact-functor K-map. -/
theorem original_flat_K_naturality {R S : CommRingCat.{u}}
    (f : R ⟶ S) [Flat (Spec.map f)] (n : ℕ)
    (a : (perfectComplexesWaldhausen (Spec R).toRingedSpace).K n) :
    (localizedStableHomotopyFunctor (n : ℤ)).map (affinePerfectBassTelescopeInitialMap S)
        (originalKStableEquiv (perfectComplexesWaldhausen (Spec S).toRingedSpace) n
          (Additive.ofMul
            (Waldhausen.KMap (perfectFlatPullback_waldhausenExact (Spec.map f)) n a))) =
      (stableHomotopyFunctor (n : ℤ)).map (boundedAboveFlatAffineSectionBassTelescopeMap f)
        ((localizedStableHomotopyFunctor (n : ℤ)).map (affinePerfectBassTelescopeInitialMap R)
          (originalKStableEquiv (perfectComplexesWaldhausen (Spec R).toRingedSpace) n
            (Additive.ofMul a))) := by
  rw [← Scheme.perfectKPullback_eq_flatPullback (Spec.map f) n]
  exact affinePerfectBassTelescopeInitialMap_originalK_naturality f n a

end ColibTest.AlgebraicGeometry.AffineBassLocalizedSpectrum
