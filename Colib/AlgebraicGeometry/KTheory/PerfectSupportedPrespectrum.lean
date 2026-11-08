/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectOpenImagePrespectrum
public import Colib.KTheory.Waldhausen.Iterated.ChosenZeroCoherence

/-!
# The actual supported prespectrum in the relative-open homotopy fiber

The native supported category and relative-acyclic category have a literal exact
flattening equivalence preserving their common ambient zero. Their original S-prespectra
are isomorphic. Transport of the original acyclic fiber map retains its whole specified
nullhomotopy, projects to the original supported inclusion, and is a stable equivalence.
The canonical zero-rebased inclusion agrees by an explicit coherent homotopy.

This completes the supported-to-relative-fiber assembly, independently of geometric roofs
or complements. It does not identify a separately prescribed image-cover spectrum, discharge
qcqs geometric hypotheses, or construct Bass nonconnective localization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology Topology.LoopPrespectrum
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual native supported S-prespectrum, with its original structure maps. -/
abbrev perfectSupportedPrespectrum := originalPrespectrum (perfectSupportedWaldhausen j)

/-- Restore relative acyclicity without changing the common chosen ambient zero. -/
def perfectSupportedToAcyclicPrespectrumMap : perfectSupportedPrespectrum j ⟶
    originalPrespectrum (Fibration.acyclicStructure (perfectOpenNested j)) :=
  originalPrespectrumMap (perfectSupportedWaldhausen j)
    (Fibration.acyclicStructure (perfectOpenNested j)) (perfectSupportedToAcyclic_exact j) rfl

/-- Flatten relative acyclicity, preserving the original zero and every S-stage. -/
def perfectAcyclicToSupportedPrespectrumMap :
    originalPrespectrum (Fibration.acyclicStructure (perfectOpenNested j)) ⟶
      perfectSupportedPrespectrum j :=
  originalPrespectrumMap (Fibration.acyclicStructure (perfectOpenNested j))
    (perfectSupportedWaldhausen j) (perfectAcyclicToSupported_exact j) rfl

/-- The literal two-sided exact flattening gives an isomorphism of the actual prespectra. -/
def perfectSupportedAcyclicPrespectrumIso : perfectSupportedPrespectrum j ≅
    originalPrespectrum (Fibration.acyclicStructure (perfectOpenNested j)) where
  hom := perfectSupportedToAcyclicPrespectrumMap j
  inv := perfectAcyclicToSupportedPrespectrumMap j
  hom_inv_id := by
    rw [perfectSupportedToAcyclicPrespectrumMap, perfectAcyclicToSupportedPrespectrumMap,
      ← originalPrespectrumMap_comp]
    exact originalPrespectrumMap_id _
  inv_hom_id := by
    rw [perfectSupportedToAcyclicPrespectrumMap, perfectAcyclicToSupportedPrespectrumMap,
      ← originalPrespectrumMap_comp]
    exact originalPrespectrumMap_id _

/-- The original supported inclusion, strictly preserving the inherited ambient zero. -/
def perfectSupportedInclusionPrespectrumMap : perfectSupportedPrespectrum j ⟶
    originalPrespectrum (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace) :=
  originalPrespectrumMap (perfectSupportedWaldhausen j)
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (perfectSupportedInclusion_isExact j) rfl

/-- The flattening square is an equality of actual prespectrum maps, not just K-maps. -/
theorem perfectSupportedToAcyclicPrespectrumMap_inclusion :
    perfectSupportedToAcyclicPrespectrumMap j ≫
      Fibration.acyclicInclusionPrespectrumMap (perfectOpenNested j) =
        perfectSupportedInclusionPrespectrumMap j := by
  exact (originalPrespectrumMap_comp (perfectSupportedWaldhausen j)
    (Fibration.acyclicStructure (perfectOpenNested j))
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (perfectSupportedToAcyclic_exact j)
    (Fibration.acyclicInclusion_exact (perfectOpenNested j)) rfl rfl).symm

/-- Canonical rebasing retains the original supported inclusion up to coherent homotopy. -/
def perfectSupportedInclusionPrespectrumRebaseHomotopy :
    LoopPrespectrum.Homotopy
      (exactOriginalPrespectrumMap (perfectSupportedWaldhausen j)
        (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (perfectSupportedInclusion_isExact j))
      (perfectSupportedInclusionPrespectrumMap j) :=
  exactOriginalPrespectrumMapChosenZeroHomotopy _ _ (perfectSupportedInclusion_isExact j) rfl

/-- Canonical rebasing likewise retains the actual supported-to-acyclic transport. -/
def perfectSupportedToAcyclicPrespectrumRebaseHomotopy :
    LoopPrespectrum.Homotopy
      (exactOriginalPrespectrumMap (perfectSupportedWaldhausen j)
        (Fibration.acyclicStructure (perfectOpenNested j)) (perfectSupportedToAcyclic_exact j))
      (perfectSupportedToAcyclicPrespectrumMap j) :=
  exactOriginalPrespectrumMapChosenZeroHomotopy _ _ (perfectSupportedToAcyclic_exact j) rfl

/-- The supported nullhomotopy is the original whole acyclic nullhomotopy precomposed. -/
def perfectSupportedPrespectrumNullhomotopy : LoopPrespectrum.Homotopy
    (perfectSupportedInclusionPrespectrumMap j ≫
      Fibration.changeWeakPrespectrumMap (perfectOpenNested j))
    (zeroHom (perfectSupportedPrespectrum j) (perfectOpenPrespectrum j)) := by
  have H := (Fibration.acyclicPrespectrumNullhomotopy (perfectOpenNested j)).precomp
    (perfectSupportedToAcyclicPrespectrumMap j)
  exact {
    level := H.level
    at_zero n x := by
      simpa only [← Category.assoc, perfectSupportedToAcyclicPrespectrumMap_inclusion]
        using H.at_zero n x
    at_one := H.at_one
    at_point := H.at_point
    comm := H.comm }

/-- Every point of the original nullhomotopy is retained, with the same time parameter. -/
theorem perfectSupportedPrespectrumNullhomotopy_level (n : ℕ)
    (s : unitInterval) (x : (perfectSupportedPrespectrum j).space n) :
    (perfectSupportedPrespectrumNullhomotopy j).level n (s, x) =
      (Fibration.acyclicPrespectrumNullhomotopy (perfectOpenNested j)).level n
        (s, (perfectSupportedToAcyclicPrespectrumMap j).map n x) := rfl

/-- Actual transport of the original canonical acyclic comparison into the coarse fiber. -/
def perfectSupportedFiberPrespectrumMap : perfectSupportedPrespectrum j ⟶
    homotopyFiber (Fibration.changeWeakPrespectrumMap (perfectOpenNested j)) :=
  perfectSupportedToAcyclicPrespectrumMap j ≫
    Fibration.canonicalFiberPrespectrumMap (perfectOpenNested j)

/-- Its source coordinate is literally the actual supported inclusion. -/
theorem perfectSupportedFiberPrespectrumMap_projection :
    perfectSupportedFiberPrespectrumMap j ≫
      homotopyFiberProjection (Fibration.changeWeakPrespectrumMap (perfectOpenNested j)) =
        perfectSupportedInclusionPrespectrumMap j := by
  rw [perfectSupportedFiberPrespectrumMap, Category.assoc,
    Fibration.canonicalFiberPrespectrumMap_projection,
    perfectSupportedToAcyclicPrespectrumMap_inclusion]

/-- Its entire fiber path is the specified original nullhomotopy, with no replacement. -/
theorem perfectSupportedFiberPrespectrumMap_path (n : ℕ)
    (x : (perfectSupportedPrespectrum j).space n) (s : unitInterval) :
    ((perfectSupportedFiberPrespectrumMap j).map n x).1.2 s =
      (perfectSupportedPrespectrumNullhomotopy j).level n (s, x) := rfl

/-- Transport equals the actual path-space lift of that supported inclusion and nullhomotopy. -/
theorem perfectSupportedFiberPrespectrumMap_eq_lift :
    perfectSupportedFiberPrespectrumMap j =
      homotopyFiberLift (Fibration.changeWeakPrespectrumMap (perfectOpenNested j))
        (perfectSupportedInclusionPrespectrumMap j)
        (perfectSupportedPrespectrumNullhomotopy j) := by
  apply LoopPrespectrum.Hom.ext
  funext n
  ext x : 1
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun f ↦ f.map n x)
      (perfectSupportedToAcyclicPrespectrumMap_inclusion j)
  · rfl

/-- Both independent parameters commute with the unchanged original structure maps. -/
theorem perfectSupportedPrespectrumNullhomotopy_structure (n : ℕ)
    (s t : unitInterval) (x : (perfectSupportedPrespectrum j).space n) :
    (perfectSupportedPrespectrumNullhomotopy j).level (n + 1)
        (s, (perfectSupportedPrespectrum j).structureMap n x t) =
      (perfectOpenPrespectrum j).structureMap n
        ((perfectSupportedPrespectrumNullhomotopy j).level n (s, x)) t :=
  (perfectSupportedPrespectrumNullhomotopy j).comm n s x t

/-- The actual supported fiber map is a stable equivalence in every integer degree. -/
theorem perfectSupportedFiberPrespectrumMap_isStableEquivalence :
    IsStableEquivalence (perfectSupportedFiberPrespectrumMap j) := by
  apply IsStableEquivalence.comp ?_
    (perfectOpen_canonicalFiberPrespectrumMap_isStableEquivalence j)
  intro d
  change IsIso ((stableHomotopyFunctor d).map (perfectSupportedAcyclicPrespectrumIso j).hom)
  infer_instance

/-- Stable supported inclusion retains the existing canonical supported K-map. -/
theorem perfectSupportedInclusionPrespectrumMap_naturality (n : ℕ)
    (a : PerfectSupportedK j n) :
    originalKStableEquiv (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace) n
        (Additive.ofMul (perfectSupportedKMap j n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (perfectSupportedInclusionPrespectrumMap j)
        (originalKStableEquiv (perfectSupportedWaldhausen j) n (Additive.ofMul a)) :=
  originalKStableEquiv_naturality _ _ (perfectSupportedInclusion_isExact j) rfl n a

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0319",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/OpenSupport.lean:54-202"
    "comparison" "The native exact support/acyclic flattening extends to actual prespectra"]
  AlgebraicGeometry.Scheme.Modules.perfectSupportedAcyclicPrespectrumIso
  AlgebraicGeometry.Scheme.Modules.perfectSupportedToAcyclicPrespectrumMap_inclusion

attribute [colib_tag "COL-0319",
  colib_ref "Waldhausen1985" "Section 1.6, Theorem 1.6.4 and proof, pp. 350-352" "adaptation"
    "The original acyclic-to-coarse-fiber comparison transported through native support"]
  AlgebraicGeometry.Scheme.Modules.perfectSupportedFiberPrespectrumMap_isStableEquivalence
  AlgebraicGeometry.Scheme.Modules.perfectSupportedFiberPrespectrumMap_projection
  AlgebraicGeometry.Scheme.Modules.perfectSupportedFiberPrespectrumMap_path
  AlgebraicGeometry.Scheme.Modules.perfectSupportedFiberPrespectrumMap_eq_lift
  AlgebraicGeometry.Scheme.Modules.perfectSupportedPrespectrumNullhomotopy_structure
  AlgebraicGeometry.Scheme.Modules.perfectSupportedInclusionPrespectrumMap_naturality
