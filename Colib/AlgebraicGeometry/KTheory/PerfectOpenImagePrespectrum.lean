/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.OpenDerivedImageCofinality
public import Colib.KTheory.Waldhausen.Iterated.StableFunctoriality
public import Colib.KTheory.Waldhausen.Fibration.SpectrumComparison

/-!
# The actual relative-open prespectrum and its restriction-image profile

The relative coarse S-prespectrum maps to the fine S-prespectrum of the open by the
original exact restriction functor. Its actual stable maps preserve the existing K-maps.
Native roofs and perfect complements imply positive bijectivity and identify degree zero
with precisely the global restriction image. Negative stable groups vanish.

The specified acyclic-to-relative-fiber map is also a stable equivalence, without geometric
roof or complement assumptions. No coherent supported-category transport to that fiber,
comparison with a separately constructed image-cover spectrum, or Bass nonconnective
localization theorem is asserted here.

The generic spectrum constructions and stable naturality are adapted from Quillen
`Waldhausen/SConstruction/Iterated/StableFunctoriality.lean` and
`Waldhausen/Fibration/SpectrumComparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. This module specializes the native constructions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology Topology.LoopPrespectrum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The original relative coarse S-prespectrum, without replacing its structure maps. -/
abbrev perfectOpenPrespectrum := originalPrespectrum (perfectOpenWeakWaldhausen j)

/-- Actual restriction of the relative coarse S-prespectrum, with canonical zero rebasing. -/
def perfectOpenRestrictPrespectrumMap : perfectOpenPrespectrum j ⟶
    originalPrespectrum (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace) :=
  exactOriginalPrespectrumMap (perfectOpenWeakWaldhausen j)
    (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace) (perfectOpenRestrict_isExact j)

/-- Stable restriction is precisely the existing relative K-map in every nonnegative degree. -/
theorem perfectOpenRestrictPrespectrumMap_naturality (n : ℕ) (a : PerfectOpenK j n) :
    originalKStableEquiv (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace) n
        (Additive.ofMul (perfectOpenKRestrict j n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (perfectOpenRestrictPrespectrumMap j)
        (originalKStableEquiv (perfectOpenWeakWaldhausen j) n (Additive.ofMul a)) :=
  originalKStableEquiv_exact_naturality (perfectOpenWeakWaldhausen j)
    (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace) (perfectOpenRestrict_isExact j) n a

/-- The relative coarse model is connective, independently of geometric comparison inputs. -/
theorem perfectOpenPrespectrum_neg_subsingleton (k : ℤ) (hk : k < 0) :
    Subsingleton (stableHomotopyGroup (perfectOpenPrespectrum j) k) :=
  originalStableHomotopyGroup_neg_subsingleton (perfectOpenWeakWaldhausen j) k hk

/-- Degree-zero stable restriction has exactly the actual global fine restriction image. -/
theorem perfectOpenRestrictPrespectrumMap_zero_mem_range_iff
    (b : (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K 0) :
    (∃ a : stableHomotopyGroup (perfectOpenPrespectrum j) 0,
      (stableHomotopyFunctor 0).map (perfectOpenRestrictPrespectrumMap j) a =
        originalKStableEquiv (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace) 0
          (Additive.ofMul b)) ↔ b ∈ PerfectOpenKZeroImage j := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨x, rfl⟩ := (originalKStableEquiv (perfectOpenWeakWaldhausen j) 0).surjective a
    have hx : perfectOpenKRestrict j 0 x.toMul = b :=
      (originalKStableEquiv (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace) 0).injective
        ((perfectOpenRestrictPrespectrumMap_naturality j 0 x.toMul).trans ha)
    change b ∈ (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0).range
    rw [← range_perfectOpenKRestrict_zero j]
    exact ⟨x.toMul, hx⟩
  · intro hb
    change b ∈ (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0).range at hb
    rw [← range_perfectOpenKRestrict_zero j] at hb
    obtain ⟨x, rfl⟩ := hb
    exact ⟨originalKStableEquiv (perfectOpenWeakWaldhausen j) 0 (Additive.ofMul x),
      (perfectOpenRestrictPrespectrumMap_naturality j 0 x).symm⟩

/-- The actual acyclic-to-relative-fiber map is a stable equivalence in all integer degrees. -/
theorem perfectOpen_canonicalFiberPrespectrumMap_isStableEquivalence :
    IsStableEquivalence (Fibration.canonicalFiberPrespectrumMap (perfectOpenNested j)) :=
  Fibration.canonicalFiberPrespectrumMap_isStableEquivalence_of_weak (perfectOpenNested j)
    (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j)

section GeometricComparison

variable [HasDerivedCategory.{d} U.Modules] [Fact (OpenDerivedImage.HasDerivedRoofs j)]
  (hc : OpenDerivedImage.HasPerfectComplements j)

include hc in
/-- Positive stable restriction is bijective, using only native roofs and perfect complements. -/
theorem perfectOpenRestrictPrespectrumMap_succ_bijective (n : ℕ) :
    Function.Bijective ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
      (perfectOpenRestrictPrespectrumMap j)) :=
  (exactStableKMap_nonnegative_bijective_iff (perfectOpenWeakWaldhausen j)
    (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)
    (perfectOpenRestrict_isExact j) (n + 1)).mpr
      (OpenDerivedImage.relativeKRestrict_succ_bijective j hc n)

/-- The actual relative stable degree-zero group identifies with the exact restriction image. -/
def perfectOpenStableZeroImageEquiv :
    stableHomotopyGroup (perfectOpenPrespectrum j) 0 ≃+ Additive (PerfectOpenKZeroImage j) :=
  (originalKStableEquiv (perfectOpenWeakWaldhausen j) 0).symm.trans
    (OpenDerivedImage.relativeKZeroImageEquiv j hc).toAdditive

/-- Forgetting image membership recovers the original stable restriction, not another map. -/
theorem perfectOpenStableZeroImageEquiv_coe
    (a : stableHomotopyGroup (perfectOpenPrespectrum j) 0) :
    originalKStableEquiv (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace) 0
        (Additive.ofMul ((perfectOpenStableZeroImageEquiv j hc a).toMul :
          (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K 0)) =
      (stableHomotopyFunctor 0).map (perfectOpenRestrictPrespectrumMap j) a := by
  have h := perfectOpenRestrictPrespectrumMap_naturality j 0
    ((originalKStableEquiv (perfectOpenWeakWaldhausen j) 0).symm a).toMul
  exact h.trans (congrArg
    (fun b => (stableHomotopyFunctor 0).map (perfectOpenRestrictPrespectrumMap j) b)
    ((originalKStableEquiv (perfectOpenWeakWaldhausen j) 0).apply_symm_apply a))

include hc in
/-- Degree-zero stable restriction is injective, without asserting surjectivity onto all K-zero. -/
theorem perfectOpenRestrictPrespectrumMap_zero_injective :
    Function.Injective ((stableHomotopyFunctor 0).map (perfectOpenRestrictPrespectrumMap j)) := by
  intro a b hab
  apply (perfectOpenStableZeroImageEquiv j hc).injective
  have h := (perfectOpenStableZeroImageEquiv_coe j hc a).trans
    (hab.trans (perfectOpenStableZeroImageEquiv_coe j hc b).symm)
  have hv := (originalKStableEquiv
    (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace) 0).injective h
  exact Subtype.ext hv

end GeometricComparison

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0318",
  colib_ref "ThomasonTrobaugh1990" "Sections 1.5.3-1.5.4, pp. 260-261" "background"
    "Actual relative coarse S-prespectrum restriction and its original stable K-map"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenRestrictPrespectrumMap
  AlgebraicGeometry.Scheme.Modules.perfectOpenRestrictPrespectrumMap_naturality

attribute [colib_tag "COL-0318"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenPrespectrum_neg_subsingleton
  AlgebraicGeometry.Scheme.Modules.perfectOpenRestrictPrespectrumMap_zero_mem_range_iff
  AlgebraicGeometry.Scheme.Modules.perfectOpenRestrictPrespectrumMap_succ_bijective
  AlgebraicGeometry.Scheme.Modules.perfectOpenStableZeroImageEquiv
  AlgebraicGeometry.Scheme.Modules.perfectOpenStableZeroImageEquiv_coe
  AlgebraicGeometry.Scheme.Modules.perfectOpenRestrictPrespectrumMap_zero_injective

attribute [colib_tag "COL-0318",
  colib_ref "Waldhausen1985" "Section 1.6, Theorem 1.6.4 and proof, pp. 350-352" "adaptation"
    "Native perfect-open relative coarse acyclic-to-fiber comparison of actual connective spectra"]
  AlgebraicGeometry.Scheme.Modules.perfectOpen_canonicalFiberPrespectrumMap_isStableEquivalence
