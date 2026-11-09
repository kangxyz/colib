/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenForget
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenPrespectrumMaps
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedFiberComparison
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedUnionFiberComparison
public import Colib.KTheory.Waldhausen.Fibration.PrespectrumNaturality

/-!
# Forgetting auxiliary support on the original localization prespectra

The literal inclusions preserve the chosen zero. They give strict change-weak and
union-support squares. Restriction uses canonical zero rebasing, so its square is
an actual coherent homotopy rather than an asserted strict equality. No geometric
compactness assumptions or stable equivalence of support forgetting are used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology Topology.LoopPrespectrum
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- Forget auxiliary support in the actual relative coarse prespectrum. -/
def perfectSupportedOpenForgetPrespectrumMap : perfectSupportedOpenPrespectrum j T ⟶
    perfectOpenPrespectrum j :=
  originalPrespectrumMap (perfectSupportedOpenWeakWaldhausen j T)
    (perfectOpenWeakWaldhausen j) (perfectSupportedInclusion_open_isExact j T) rfl

/-- Forget auxiliary support while retaining vanishing on the specified open. -/
def perfectSupportedUnionForgetPrespectrumMap : perfectSupportedUnionPrespectrum j T ⟶
    perfectSupportedPrespectrum j :=
  originalPrespectrumMap (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι)
    (perfectSupportedWaldhausen j) (perfectSupportedUnionForget_isExact j T) rfl

/-- Both change-weak routes are the same map at every original S-stage. -/
theorem perfectSupportedOpenForgetPrespectrumMap_changeWeak :
    Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T) ≫
        perfectSupportedOpenForgetPrespectrumMap j T =
      perfectSupportedInclusionPrespectrumMap T.ι ≫
        Fibration.changeWeakPrespectrumMap (perfectOpenNested j) := by
  unfold Fibration.changeWeakPrespectrumMap perfectSupportedOpenForgetPrespectrumMap
    perfectSupportedInclusionPrespectrumMap
  erw [← originalPrespectrumMap_comp, ← originalPrespectrumMap_comp]
  rfl

/-- The union-to-base square is strict, retaining the actual supported inclusions. -/
theorem perfectSupportedUnionForgetPrespectrumMap_inclusion :
    perfectSupportedUnionInclusionPrespectrumMap j T ≫
        perfectSupportedInclusionPrespectrumMap T.ι =
      perfectSupportedUnionForgetPrespectrumMap j T ≫
        perfectSupportedInclusionPrespectrumMap j := by
  unfold perfectSupportedUnionInclusionPrespectrumMap perfectSupportedInclusionPrespectrumMap
    perfectSupportedUnionForgetPrespectrumMap
  erw [← originalPrespectrumMap_comp, ← originalPrespectrumMap_comp]

/-- Canonical zero rebasing of the relative support-forgetting map. -/
def perfectSupportedOpenForgetPrespectrumRebaseHomotopy : LoopPrespectrum.Homotopy
    (exactOriginalPrespectrumMap (perfectSupportedOpenWeakWaldhausen j T)
      (perfectOpenWeakWaldhausen j) (perfectSupportedInclusion_open_isExact j T))
    (perfectSupportedOpenForgetPrespectrumMap j T) :=
  exactOriginalPrespectrumMapChosenZeroHomotopy _ _
    (perfectSupportedInclusion_open_isExact j T) rfl

/-- Canonical zero rebasing of the union support-forgetting map. -/
def perfectSupportedUnionForgetPrespectrumRebaseHomotopy : LoopPrespectrum.Homotopy
    (exactOriginalPrespectrumMap (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι)
      (perfectSupportedWaldhausen j) (perfectSupportedUnionForget_isExact j T))
    (perfectSupportedUnionForgetPrespectrumMap j T) :=
  exactOriginalPrespectrumMapChosenZeroHomotopy _ _
    (perfectSupportedUnionForget_isExact j T) rfl

/-- Supported restriction commutes with forgetting via the actual composition and rebase tracks. -/
def perfectSupportedOpenForgetPrespectrumRestrictHomotopy : LoopPrespectrum.Homotopy
    (perfectSupportedOpenForgetPrespectrumMap j T ≫ perfectOpenRestrictPrespectrumMap j)
    (perfectSupportedOpenRestrictPrespectrumMap j T ≫
      perfectSupportedInclusionPrespectrumMap (j ⁻¹ᵁ T).ι) := by
  let H₁ := (perfectSupportedOpenForgetPrespectrumRebaseHomotopy j T).symm.postcomp
    (perfectOpenRestrictPrespectrumMap j)
  let H₂ := exactOriginalPrespectrumMapCompHomotopy
    (perfectSupportedOpenWeakWaldhausen j T) (perfectOpenWeakWaldhausen j)
    (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)
    (perfectSupportedInclusion_open_isExact j T) (perfectOpenRestrict_isExact j)
  let H₃ := exactOriginalPrespectrumMapCompHomotopy
    (perfectSupportedOpenWeakWaldhausen j T) (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι)
    (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)
    (perfectSupportedOpenRestrict_waldhausenExact j T)
    (perfectSupportedInclusion_isExact (j ⁻¹ᵁ T).ι)
  let H₄ := (perfectSupportedInclusionPrespectrumRebaseHomotopy (j ⁻¹ᵁ T).ι).precomp
    (perfectSupportedOpenRestrictPrespectrumMap j T)
  exact ((H₁.trans H₂.symm).trans H₃).trans H₄

/-- The literal change-weak square, as an arrow in the actual prespectrum category. -/
def perfectSupportedOpenForgetPrespectrumSquare :
    Arrow.mk (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T)) ⟶
      Arrow.mk (Fibration.changeWeakPrespectrumMap (perfectOpenNested j)) :=
  Arrow.homMk (perfectSupportedInclusionPrespectrumMap T.ι)
    (perfectSupportedOpenForgetPrespectrumMap j T)
    (perfectSupportedOpenForgetPrespectrumMap_changeWeak j T).symm

/-- The induced actual homotopy-fiber map retains source points and complete paths. -/
def perfectSupportedOpenForgetFiberPrespectrumMap :=
  homotopyFiberMap (perfectSupportedOpenForgetPrespectrumSquare j T)

/-- Its projection is the original support-forgetting inclusion. -/
theorem perfectSupportedOpenForgetFiberPrespectrumMap_projection :
    perfectSupportedOpenForgetFiberPrespectrumMap j T ≫
        homotopyFiberProjection (Fibration.changeWeakPrespectrumMap (perfectOpenNested j)) =
      homotopyFiberProjection
        (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T)) ≫
          perfectSupportedInclusionPrespectrumMap T.ι :=
  homotopyFiberProjection_naturality (perfectSupportedOpenForgetPrespectrumSquare j T)

/-- Every point of the path is carried by the original coarse forgetting map. -/
theorem perfectSupportedOpenForgetFiberPrespectrumMap_path (n : ℕ)
    (z : (homotopyFiber
      (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T))).space n)
    (s : unitInterval) :
    ((perfectSupportedOpenForgetFiberPrespectrumMap j T).map n z).1.2 s =
      (perfectSupportedOpenForgetPrespectrumMap j T).map n (z.1.2 s) := rfl

/-- The signed stable connecting map is natural for the actual fiber square. -/
theorem perfectSupportedOpenForgetFiberPrespectrumMap_connecting (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (perfectSupportedOpenForgetPrespectrumMap j T) ≫
        stableFiberConnecting (Fibration.changeWeakPrespectrumMap (perfectOpenNested j)) d =
      stableFiberConnecting
        (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T)) d ≫
          (stableHomotopyFunctor d).map (perfectSupportedOpenForgetFiberPrespectrumMap j T) :=
  stableFiberConnecting_naturality (perfectSupportedOpenForgetPrespectrumSquare j T) d

/-- Stable coarse forgetting is the existing COL-0336 K-map, including degree zero. -/
theorem perfectSupportedOpenForgetPrespectrumMap_naturality (n : ℕ)
    (a : PerfectSupportedOpenCoarseK j T n) :
    originalKStableEquiv (perfectOpenWeakWaldhausen j) n
        (Additive.ofMul (perfectSupportedOpenKForget j T n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (perfectSupportedOpenForgetPrespectrumMap j T)
        (originalKStableEquiv (perfectSupportedOpenWeakWaldhausen j T) n (Additive.ofMul a)) :=
  originalKStableEquiv_naturality _ _ (perfectSupportedInclusion_open_isExact j T) rfl n a

/-- Stable union forgetting is the existing COL-0336 K-map, including degree zero. -/
theorem perfectSupportedUnionForgetPrespectrumMap_naturality (n : ℕ)
    (a : PerfectSupportedK (T ⊔ j.opensRange).ι n) :
    originalKStableEquiv (perfectSupportedWaldhausen j) n
        (Additive.ofMul (perfectSupportedUnionForgetKMap j T n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (perfectSupportedUnionForgetPrespectrumMap j T)
        (originalKStableEquiv (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι) n
          (Additive.ofMul a)) :=
  originalKStableEquiv_naturality _ _ (perfectSupportedUnionForget_isExact j T) rfl n a

/-- The actual induced acyclic functor agrees strictly with union-support forgetting. -/
theorem perfectSupportedUnionForgetPrespectrumMap_toAcyclic :
    perfectSupportedUnionToAcyclicPrespectrumMap j T ≫
        originalPrespectrumMap
          (Fibration.acyclicStructure (perfectSupportedOpenNested j T))
          (Fibration.acyclicStructure (perfectOpenNested j))
          (Fibration.acyclicFunctor_exact (perfectSupportedOpenNested j T) (perfectOpenNested j)
            (perfectSupportedInclusion_isExact T.ι)
            (perfectSupportedInclusion_open_isExact j T)) rfl =
      perfectSupportedUnionForgetPrespectrumMap j T ≫
        perfectSupportedToAcyclicPrespectrumMap j := by
  unfold perfectSupportedUnionToAcyclicPrespectrumMap perfectSupportedUnionForgetPrespectrumMap
    perfectSupportedToAcyclicPrespectrumMap
  erw [← originalPrespectrumMap_comp, ← originalPrespectrumMap_comp]

/-- Forgetting preserves every point of the original supported null, at every S-stage. -/
theorem perfectSupportedUnionPrespectrumNullhomotopy_forget (n : ℕ) (s : unitInterval)
    (x : (perfectSupportedUnionPrespectrum j T).space n) :
    (perfectSupportedOpenForgetPrespectrumMap j T).map n
        ((perfectSupportedUnionPrespectrumNullhomotopy j T).level n (s, x)) =
      (perfectSupportedPrespectrumNullhomotopy j).level n
        (s, (perfectSupportedUnionForgetPrespectrumMap j T).map n x) := by
  have h := Fibration.acyclicPrespectrumNullhomotopy_natural
    (perfectSupportedOpenNested j T) (perfectOpenNested j)
    (perfectSupportedInclusion_isExact T.ι) (perfectSupportedInclusion_open_isExact j T)
    rfl n s ((perfectSupportedUnionToAcyclicPrespectrumMap j T).map n x)
  have he := congrArg (fun f ↦ f.map n x)
    (perfectSupportedUnionForgetPrespectrumMap_toAcyclic j T)
  exact h.trans (congrArg
    (fun y ↦ (Fibration.acyclicPrespectrumNullhomotopy (perfectOpenNested j)).level n (s, y)) he)

/-- Null time and structure time remain independent throughout the forgetting square. -/
theorem perfectSupportedUnionPrespectrumNullhomotopy_forget_structure (n : ℕ)
    (s t : unitInterval) (x : (perfectSupportedUnionPrespectrum j T).space n) :
    (perfectSupportedOpenForgetPrespectrumMap j T).map (n + 1)
        ((perfectSupportedUnionPrespectrumNullhomotopy j T).level (n + 1)
          (s, (perfectSupportedUnionPrespectrum j T).structureMap n x t)) =
      (perfectOpenPrespectrum j).structureMap n
        ((perfectSupportedPrespectrumNullhomotopy j).level n
          (s, (perfectSupportedUnionForgetPrespectrumMap j T).map n x)) t := by
  rw [perfectSupportedUnionPrespectrumNullhomotopy_structure]
  exact (congrArg (fun p ↦ p t) ((perfectSupportedOpenForgetPrespectrumMap j T).comm n
    ((perfectSupportedUnionPrespectrumNullhomotopy j T).level n (s, x)))).trans
      (congrArg (fun y ↦ (perfectOpenPrespectrum j).structureMap n y t)
        (perfectSupportedUnionPrespectrumNullhomotopy_forget j T n s x))

/-- The original supported fiber lifts commute strictly, with the proven whole null. -/
theorem perfectSupportedUnionFiberPrespectrumMap_forget :
    perfectSupportedUnionFiberPrespectrumMap j T ≫
        perfectSupportedOpenForgetFiberPrespectrumMap j T =
      perfectSupportedUnionForgetPrespectrumMap j T ≫
        perfectSupportedFiberPrespectrumMap j := by
  rw [perfectSupportedUnionFiberPrespectrumMap_eq_lift,
    perfectSupportedFiberPrespectrumMap_eq_lift]
  exact homotopyFiberLift_naturality
    (perfectSupportedUnionInclusionPrespectrumMap j T)
    (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T))
    (perfectSupportedInclusionPrespectrumMap j)
    (Fibration.changeWeakPrespectrumMap (perfectOpenNested j))
    (perfectSupportedUnionPrespectrumNullhomotopy j T)
    (perfectSupportedPrespectrumNullhomotopy j)
    (perfectSupportedUnionForgetPrespectrumMap j T)
    (perfectSupportedInclusionPrespectrumMap T.ι)
    (perfectSupportedOpenForgetPrespectrumMap j T)
    (perfectSupportedUnionForgetPrespectrumMap_inclusion j T)
    (perfectSupportedOpenForgetPrespectrumMap_changeWeak j T).symm
    (perfectSupportedUnionPrespectrumNullhomotopy_forget j T)

/-- Canonically rebased supported fiber presentations commute by an actual coherent homotopy. -/
def perfectSupportedUnionFiberPrespectrumRebasedForgetHomotopy : LoopPrespectrum.Homotopy
    (perfectSupportedUnionFiberPrespectrumRebasedMap j T ≫
      perfectSupportedOpenForgetFiberPrespectrumMap j T)
    (perfectSupportedUnionForgetPrespectrumMap j T ≫
      perfectSupportedFiberPrespectrumRebasedMap j) := by
  have H := (perfectSupportedUnionFiberPrespectrumRebaseHomotopy j T).postcomp
    (perfectSupportedOpenForgetFiberPrespectrumMap j T)
  rw [perfectSupportedUnionFiberPrespectrumMap_forget] at H
  exact H.trans ((perfectSupportedFiberPrespectrumRebaseHomotopy j).symm.precomp
    (perfectSupportedUnionForgetPrespectrumMap j T))

/-- Level one recovers the actual coarse delooping map, not an alternative comparison. -/
theorem perfectSupportedOpenForgetPrespectrumMap_level_one_square :
    (perfectOpenWeakWaldhausen j).asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun.comp
        (deloopingMap (perfectSupportedInclusion_open_isExact j T)).hom =
      ((perfectSupportedOpenForgetPrespectrumMap j T).map 1).comp
        (perfectSupportedOpenWeakWaldhausen j T).asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun :=
  asSmallDeloopingHomeomorph_naturality (perfectSupportedInclusion_open_isExact j T)

/-- Level one recovers the actual union-support delooping map. -/
theorem perfectSupportedUnionForgetPrespectrumMap_level_one_square :
    (perfectSupportedWaldhausen j).asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun.comp
        (deloopingMap (perfectSupportedUnionForget_isExact j T)).hom =
      ((perfectSupportedUnionForgetPrespectrumMap j T).map 1).comp
        (perfectSupportedWaldhausen
          (T ⊔ j.opensRange).ι).asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun :=
  asSmallDeloopingHomeomorph_naturality (perfectSupportedUnionForget_isExact j T)

attribute [colib_tag "COL-0337",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Forget.lean:30-92"
    "comparison" "Actual support-forgetting maps lifted to the whole original prespectrum"]
  perfectSupportedOpenForgetPrespectrumMap
  perfectSupportedUnionForgetPrespectrumMap
  perfectSupportedOpenForgetPrespectrumMap_changeWeak
  perfectSupportedUnionForgetPrespectrumMap_inclusion
  perfectSupportedUnionForgetPrespectrumMap_toAcyclic
  perfectSupportedOpenForgetPrespectrumRestrictHomotopy
  perfectSupportedUnionPrespectrumNullhomotopy_forget
  perfectSupportedUnionPrespectrumNullhomotopy_forget_structure
  perfectSupportedUnionFiberPrespectrumMap_forget
  perfectSupportedOpenForgetFiberPrespectrumMap_connecting
  perfectSupportedOpenForgetPrespectrumMap_naturality
  perfectSupportedUnionForgetPrespectrumMap_naturality

end AlgebraicGeometry.Scheme.Modules
