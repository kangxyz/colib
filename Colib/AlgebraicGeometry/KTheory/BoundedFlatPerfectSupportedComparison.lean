/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectSupportedApproximation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumComparison
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedPrespectrum
public import Colib.KTheory.Waldhausen.Iterated.ExactCoherence

/-!
# The actual supported bounded-flat to perfect comparison

On compact schemes, the literal supported inclusion induces the unchanged equivalence on
connective K-groups, including K-zero, and a stable equivalence of its actual normalized
prespectrum map. The support-forgetting square retains its actual maps and coherent homotopy.
This is a model comparison, not Bass nonconnective localization or a levelwise equivalence.

Adapted from Quillen `BoundedFlat/SupportComparison.lean:104-140` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, with the native actual stable-map comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.RingedSpace Topology Topology.LoopPrespectrum

universe u
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Connective K-theory of the actual supported bounded-above-flat model. -/
abbrev BoundedAboveFlatPerfectSupportedK (n : ℕ) :=
  (boundedAboveFlatPerfectSupportedWaldhausen j).K n

/-- The original inclusion induces this specified forward K-map. -/
def boundedAboveFlatPerfectSupportedToPerfectKMap (n : ℕ) :
    BoundedAboveFlatPerfectSupportedK j n →* PerfectSupportedK j n :=
  KMap (boundedAboveFlatPerfectSupportedInclusion_isExact j) n

/-- Supported approximation gives bijectivity in every natural degree, including zero. -/
@[colib_tag "COL-0382",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportComparison.lean:104-113"
    "adaptation"
    "Actual supported inclusion K-map bijectivity for a scheme with compact underlying space"]
theorem boundedAboveFlatPerfectSupportedToPerfectKMap_bijective [CompactSpace X] (n : ℕ) :
    Function.Bijective (boundedAboveFlatPerfectSupportedToPerfectKMap j n) := by
  let : (complexes X.Modules).weq.HasTwoOutOfThreeProperty := by
    change (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)).HasTwoOutOfThreeProperty
    infer_instance
  let : (perfectSupportedWaldhausen j).weq.HasTwoOutOfThreeProperty :=
    CofibrationClosedSubcategory.twoOutOfThree _ _ _
  exact (boundedAboveFlatPerfectSupportedInclusion_approximation j).KMap_bijective_general
    (boundedAboveFlatPerfectSupportedInclusion_isExact j)
    (boundedAboveFlatPerfectSupportedJointData j) n

/-- The equivalence has the literal supported inclusion as its forward homomorphism. -/
@[colib_tag "COL-0382",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportComparison.lean:115-125"
    "adaptation"
    "The actual supported inclusion K-equivalence with its specified forward K-map"]
def boundedAboveFlatPerfectSupportedKEquiv [CompactSpace X] (n : ℕ) :
    BoundedAboveFlatPerfectSupportedK j n ≃* PerfectSupportedK j n :=
  MulEquiv.ofBijective (boundedAboveFlatPerfectSupportedToPerfectKMap j n)
    (boundedAboveFlatPerfectSupportedToPerfectKMap_bijective j n)

/-- The equivalence does not replace the original inclusion map, including at K-zero. -/
@[simp] theorem boundedAboveFlatPerfectSupportedKEquiv_coe [CompactSpace X] (n : ℕ) :
    (↑(boundedAboveFlatPerfectSupportedKEquiv j n) :
      BoundedAboveFlatPerfectSupportedK j n →* PerfectSupportedK j n) =
        boundedAboveFlatPerfectSupportedToPerfectKMap j n := rfl

/-- Forget the same support condition on the original bounded-flat K-groups. -/
def boundedAboveFlatPerfectSupportedForgetKMap (n : ℕ) :
    BoundedAboveFlatPerfectSupportedK j n →* X.toRingedSpace.boundedAboveFlatPerfectK n :=
  KMap (boundedAboveFlatPerfectSupportedForget_isExact j) n

/-- Both actual inclusion/forgetting routes induce exactly the same homomorphism. -/
@[colib_tag "COL-0382",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportComparison.lean:129-140"
    "adaptation" "The literal support-forgetting square with unchanged canonical K-maps"]
theorem boundedAboveFlatPerfectSupportedToPerfectKMap_forget (n : ℕ) :
    (perfectSupportedKMap j n).comp (boundedAboveFlatPerfectSupportedToPerfectKMap j n) =
      (boundedAboveFlatPerfectToPerfectKMap X.toRingedSpace n).comp
        (boundedAboveFlatPerfectSupportedForgetKMap j n) := by
  exact (KMap_comp_KMap (boundedAboveFlatPerfectSupportedInclusion_isExact j)
    (perfectSupportedInclusion_isExact j) n).trans
    (KMap_comp_KMap (boundedAboveFlatPerfectSupportedForget_isExact j)
      (boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace) n).symm

/-- Canonical zero normalization of the actual supported inclusion. -/
def boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap :
    originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j) ⟶
      perfectSupportedPrespectrum j :=
  exactOriginalPrespectrumMap _ _ (boundedAboveFlatPerfectSupportedInclusion_isExact j)

/-- The specified inclusion map is a stable equivalence in every integer degree. -/
@[colib_tag "COL-0382",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportComparison.lean:104-113"
    "ingredient"
    "Supported inclusion K-bijection input; integer stable equivalence is derived using the \
    native original-prespectrum comparison, not stated in this source"]
theorem boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap_isStableEquivalence
    [CompactSpace X] :
    IsStableEquivalence (boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap j) :=
  (exactOriginalPrespectrumMap_isStableEquivalence_iff _ _
    (boundedAboveFlatPerfectSupportedInclusion_isExact j)).mpr
      (boundedAboveFlatPerfectSupportedToPerfectKMap_bijective j)

/-- The actual stable inclusion retains the original forward K-map. -/
theorem boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap_originalK_naturality
    (n : ℕ) (a : BoundedAboveFlatPerfectSupportedK j n) :
    originalKStableEquiv (perfectSupportedWaldhausen j) n
        (Additive.ofMul (boundedAboveFlatPerfectSupportedToPerfectKMap j n a)) =
      (stableHomotopyFunctor (n : ℤ)).map
        (boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap j)
        (originalKStableEquiv (boundedAboveFlatPerfectSupportedWaldhausen j) n
          (Additive.ofMul a)) :=
  originalKStableEquiv_exact_naturality _ _
    (boundedAboveFlatPerfectSupportedInclusion_isExact j) n a

/-- The actual zero-space inclusion retains the same K-map in every connective degree. -/
theorem boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap_zeroSpace_naturality
    (n : ℕ) (a : BoundedAboveFlatPerfectSupportedK j n) :
    originalZeroSpaceEquiv (perfectSupportedWaldhausen j) n
        (boundedAboveFlatPerfectSupportedToPerfectKMap j n a) =
      HomotopyGroup.map ((boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap j).map 0)
        ((boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap j).map_point 0)
        (originalZeroSpaceEquiv (boundedAboveFlatPerfectSupportedWaldhausen j) n a) :=
  exactOriginalZeroSpaceEquiv_naturality _ _
    (boundedAboveFlatPerfectSupportedInclusion_isExact j) n a

/-- Canonical zero normalization of the unchanged support-forgetting functor. -/
def boundedAboveFlatPerfectSupportedForgetPrespectrumMap :
    originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j) ⟶
      originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) :=
  exactOriginalPrespectrumMap _ _ (boundedAboveFlatPerfectSupportedForget_isExact j)

/-- The actual square commutes by a whole coherent homotopy, not a false strict rebase law. -/
@[colib_tag "COL-0382",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportComparison.lean:129-140"
    "ingredient"
    "Literal support-forgetting square input; whole coherent homotopy is derived using native \
    exact composition and chosen-zero rebase homotopies, not stated in this source"]
def boundedAboveFlatPerfectSupportedToPerfectPrespectrumForgetHomotopy :
    Homotopy
      (boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap j ≫
        perfectSupportedInclusionPrespectrumMap j)
      (boundedAboveFlatPerfectSupportedForgetPrespectrumMap j ≫
        boundedAboveFlatPerfectToPerfectPrespectrumMap X.toRingedSpace) := by
  let hI := boundedAboveFlatPerfectSupportedInclusion_isExact j
  let hS := perfectSupportedInclusion_isExact j
  let hF := boundedAboveFlatPerfectSupportedForget_isExact j
  let hB := boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace
  let H := exactOriginalPrespectrumIsoHomotopy _ _ (hI.comp hS) (hF.comp hB)
    (eqToIso (boundedAboveFlatPerfectSupportedInclusion_forget j))
  exact ((perfectSupportedInclusionPrespectrumRebaseHomotopy j).precomp
      (boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap j)).symm.trans
    ((exactOriginalPrespectrumMapCompHomotopy _ _ _ hI hS).symm.trans
      (H.trans (exactOriginalPrespectrumMapCompHomotopy _ _ _ hF hB)))

/-- Every integer stable degree sees the same actual support-forgetting square. -/
theorem boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap_forget_stable (d : ℤ) :
    (stableHomotopyFunctor d).map
        (boundedAboveFlatPerfectSupportedToPerfectPrespectrumMap j ≫
          perfectSupportedInclusionPrespectrumMap j) =
      (stableHomotopyFunctor d).map
        (boundedAboveFlatPerfectSupportedForgetPrespectrumMap j ≫
          boundedAboveFlatPerfectToPerfectPrespectrumMap X.toRingedSpace) :=
  (boundedAboveFlatPerfectSupportedToPerfectPrespectrumForgetHomotopy j).stableHomotopyMap_eq d

end AlgebraicGeometry.Scheme.Modules
