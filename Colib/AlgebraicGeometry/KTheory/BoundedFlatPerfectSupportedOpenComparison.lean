/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedOpen
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedComparison
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenPrespectrumMaps

/-!
# The actual supported relative-open bounded-flat comparison

The literal inclusion into the existing relative perfect category induces bijections
on all connective K-groups, including zero. Its specified normalized prespectrum map
is a stable equivalence. The original change-of-weak-equivalences square is realized
by a whole coherent homotopy, keeping the original maps on both sides.

Adapted from Quillen `BoundedFlat/SupportedOpenComparison.lean:78-122` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The stable map and whole homotopy are native
extensions of the K-comparison and square, not Bass nonconnective localization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS Topology Topology.LoopPrespectrum

universe u
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The actual connective groups of the supported bounded-flat relative-open model. -/
abbrev BoundedAboveFlatPerfectSupportedOpenK (n : ℕ) :=
  (boundedAboveFlatPerfectSupportedOpenWaldhausen j T).K n

/-- The original identity functor enlarges the actual weak class. -/
def boundedAboveFlatPerfectSupportedOpenKMap (n : ℕ) :
    BoundedAboveFlatPerfectSupportedK T.ι n →* BoundedAboveFlatPerfectSupportedOpenK j T n :=
  KMap (changeWeak_exact (boundedAboveFlatPerfectSupportedOpenNested j T)) n

/-- The literal supported inclusion induces this specified relative K-map. -/
def boundedAboveFlatPerfectSupportedOpenToPerfectKMap (n : ℕ) :
    BoundedAboveFlatPerfectSupportedOpenK j T n →* PerfectSupportedOpenCoarseK j T n :=
  KMap (boundedAboveFlatPerfectSupportedOpenInclusion_isExact j T) n

/-- Genuine coarse joint data and actual approximation give bijectivity, including K-zero. -/
@[colib_tag "COL-0505",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenComparison.lean:93-99"
    "adaptation"
    "Bijectivity of the actual relative inclusion K-map, including degree zero"]
theorem boundedAboveFlatPerfectSupportedOpenToPerfectKMap_bijective [CompactSpace X] (n : ℕ) :
    Function.Bijective (boundedAboveFlatPerfectSupportedOpenToPerfectKMap j T n) :=
  (boundedAboveFlatPerfectSupportedOpenInclusion_approximation j T).KMap_bijective_general
    (boundedAboveFlatPerfectSupportedOpenInclusion_isExact j T)
    ((boundedAboveFlatPerfectSupportedOpenJointData j T).coarseReflexive
      (boundedAboveFlatPerfectSupportedOpenNested j T)) n

/-- The relative equivalence retains the actual original inclusion as its forward map. -/
@[colib_tag "COL-0505",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenComparison.lean:102-110"
    "adaptation"
    "Relative supported K-equivalence with its original inclusion as forward map"]
def boundedAboveFlatPerfectSupportedOpenKEquiv [CompactSpace X] (n : ℕ) :
    BoundedAboveFlatPerfectSupportedOpenK j T n ≃* PerfectSupportedOpenCoarseK j T n :=
  MulEquiv.ofBijective (boundedAboveFlatPerfectSupportedOpenToPerfectKMap j T n)
    (boundedAboveFlatPerfectSupportedOpenToPerfectKMap_bijective j T n)

/-- The canonical forward homomorphism is unchanged in every connective degree. -/
@[simp] theorem boundedAboveFlatPerfectSupportedOpenKEquiv_coe [CompactSpace X] (n : ℕ) :
    (↑(boundedAboveFlatPerfectSupportedOpenKEquiv j T n) :
      BoundedAboveFlatPerfectSupportedOpenK j T n →* PerfectSupportedOpenCoarseK j T n) =
        boundedAboveFlatPerfectSupportedOpenToPerfectKMap j T n := rfl

/-- Both routes use exactly the original inclusion and change-of-weak K-maps. -/
@[colib_tag "COL-0505",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenComparison.lean:114-122"
    "adaptation"
    "Original change-of-weak and inclusion K-maps commute"]
theorem boundedAboveFlatPerfectSupportedOpenToPerfectKMap_changeWeak (n : ℕ) :
    (boundedAboveFlatPerfectSupportedOpenToPerfectKMap j T n).comp
        (boundedAboveFlatPerfectSupportedOpenKMap j T n) =
      (perfectSupportedOpenKMap j T n).comp
        (boundedAboveFlatPerfectSupportedToPerfectKMap T.ι n) :=
  (KMap_comp_KMap (changeWeak_exact (boundedAboveFlatPerfectSupportedOpenNested j T))
    (boundedAboveFlatPerfectSupportedOpenInclusion_isExact j T) n).trans
      (KMap_comp_KMap (boundedAboveFlatPerfectSupportedInclusion_isExact T.ι)
        (changeWeak_exact (perfectSupportedOpenNested j T)) n).symm

/-- The actual relative inclusion with its canonical zero normalization. -/
def boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap :
    originalPrespectrum (boundedAboveFlatPerfectSupportedOpenWaldhausen j T) ⟶
      perfectSupportedOpenPrespectrum j T :=
  exactOriginalPrespectrumMap _ _ (boundedAboveFlatPerfectSupportedOpenInclusion_isExact j T)

/-- The specified inclusion map is an equivalence on every integer stable group. -/
@[colib_tag "COL-0505",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenComparison.lean:93-99"
    "ingredient"
    "Original relative K-bijection input; the native prespectrum comparison derives \
    stable equivalence"]
theorem boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap_isStableEquivalence
    [CompactSpace X] :
    IsStableEquivalence (boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap j T) :=
  (exactOriginalPrespectrumMap_isStableEquivalence_iff _ _
    (boundedAboveFlatPerfectSupportedOpenInclusion_isExact j T)).mpr
      (boundedAboveFlatPerfectSupportedOpenToPerfectKMap_bijective j T)

/-- Stable comparison retains the actual original forward K-map, including at zero. -/
theorem boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap_originalK_naturality
    (n : ℕ) (a : BoundedAboveFlatPerfectSupportedOpenK j T n) :
    originalKStableEquiv (perfectSupportedOpenWeakWaldhausen j T) n
        (Additive.ofMul (boundedAboveFlatPerfectSupportedOpenToPerfectKMap j T n a)) =
      (stableHomotopyFunctor (n : ℤ)).map
        (boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap j T)
        (originalKStableEquiv (boundedAboveFlatPerfectSupportedOpenWaldhausen j T) n
          (Additive.ofMul a)) :=
  originalKStableEquiv_exact_naturality _ _
    (boundedAboveFlatPerfectSupportedOpenInclusion_isExact j T) n a

/-- The original change-of-weak maps commute with inclusion by a whole coherent homotopy. -/
@[colib_tag "COL-0505",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenComparison.lean:114-122"
    "ingredient"
    "Original K-square input; native zero normalization and composition derive a new \
    whole homotopy"]
def boundedAboveFlatPerfectSupportedOpenChangeWeakHomotopy : Homotopy
    (changeWeakPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j T) ≫
      boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap j T)
    (boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap T.ι ≫
      changeWeakPrespectrumMap (perfectSupportedOpenNested j T)) := by
  let hS := changeWeak_exact (boundedAboveFlatPerfectSupportedOpenNested j T)
  let hC := boundedAboveFlatPerfectSupportedOpenInclusion_isExact j T
  let hI := boundedAboveFlatPerfectSupportedInclusion_isExact T.ι
  let hT := changeWeak_exact (perfectSupportedOpenNested j T)
  let H := exactOriginalPrespectrumIsoHomotopy _ _ (hS.comp hC) (hI.comp hT) (Iso.refl _)
  exact ((exactOriginalPrespectrumMapChosenZeroHomotopy _ _ hS rfl).symm.postcomp
      (boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap j T)).trans
    ((exactOriginalPrespectrumMapCompHomotopy _ _ _ hS hC).symm.trans
      (H.trans ((exactOriginalPrespectrumMapCompHomotopy _ _ _ hI hT).trans
        ((exactOriginalPrespectrumMapChosenZeroHomotopy _ _ hT rfl).precomp
          (boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap T.ι)))))

/-- Every integer stable degree sees the square of the original actual maps. -/
theorem boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap_changeWeak_stable (d : ℤ) :
    (stableHomotopyFunctor d).map
        (changeWeakPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j T) ≫
          boundedAboveFlatPerfectSupportedOpenToPerfectPrespectrumMap j T) =
      (stableHomotopyFunctor d).map
        (boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap T.ι ≫
          changeWeakPrespectrumMap (perfectSupportedOpenNested j T)) :=
  (boundedAboveFlatPerfectSupportedOpenChangeWeakHomotopy j T).stableHomotopyMap_eq d

end AlgebraicGeometry.Scheme.Modules
