/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenLongExactSequence
public import Colib.KTheory.Waldhausen.Fibration.SpectrumComparison
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

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The actual supported relative-coarse S-prespectrum. -/
abbrev perfectSupportedOpenPrespectrum :=
  originalPrespectrum (perfectSupportedOpenWeakWaldhausen j T)

/-- The original supported coarse-fiber comparison is stable in every integer degree. -/
theorem perfectSupportedOpen_canonicalFiberPrespectrumMap_isStableEquivalence :
    IsStableEquivalence (Fibration.canonicalFiberPrespectrumMap
      (perfectSupportedOpenNested j T)) :=
  Fibration.canonicalFiberPrespectrumMap_isStableEquivalence_of_weak
    (perfectSupportedOpenNested j T)
    (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T)

/-- The actual native supported S-prespectrum, with its original structure maps. -/
abbrev perfectSupportedUnionPrespectrum := originalPrespectrum (perfectSupportedWaldhausen (T ⊔
  j.opensRange).ι)

/-- Restore relative acyclicity without changing the common chosen ambient zero. -/
def perfectSupportedUnionToAcyclicPrespectrumMap : perfectSupportedUnionPrespectrum j T ⟶
    originalPrespectrum (Fibration.acyclicStructure (perfectSupportedOpenNested j T)) :=
  originalPrespectrumMap (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι)
    (Fibration.acyclicStructure (perfectSupportedOpenNested j T))
      (perfectSupportedUnionToAcyclic_exact j T) rfl

/-- Flatten relative acyclicity, preserving the original zero and every S-stage. -/
def perfectSupportedOpenAcyclicToSupportedPrespectrumMap :
    originalPrespectrum (Fibration.acyclicStructure (perfectSupportedOpenNested j T)) ⟶
      perfectSupportedUnionPrespectrum j T :=
  originalPrespectrumMap (Fibration.acyclicStructure (perfectSupportedOpenNested j T))
    (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι)
      (perfectSupportedOpenAcyclicToSupported_exact j T) rfl

/-- The literal two-sided exact flattening gives an isomorphism of the actual prespectra. -/
def perfectSupportedUnionAcyclicPrespectrumIso : perfectSupportedUnionPrespectrum j T ≅
    originalPrespectrum (Fibration.acyclicStructure (perfectSupportedOpenNested j T)) where
  hom := perfectSupportedUnionToAcyclicPrespectrumMap j T
  inv := perfectSupportedOpenAcyclicToSupportedPrespectrumMap j T
  hom_inv_id := by
    rw [perfectSupportedUnionToAcyclicPrespectrumMap,
      perfectSupportedOpenAcyclicToSupportedPrespectrumMap,
      ← originalPrespectrumMap_comp]
    exact originalPrespectrumMap_id _
  inv_hom_id := by
    rw [perfectSupportedUnionToAcyclicPrespectrumMap,
      perfectSupportedOpenAcyclicToSupportedPrespectrumMap,
      ← originalPrespectrumMap_comp]
    exact originalPrespectrumMap_id _

/-- The original supported inclusion, strictly preserving the inherited ambient zero. -/
def perfectSupportedUnionInclusionPrespectrumMap : perfectSupportedUnionPrespectrum j T ⟶
    originalPrespectrum (perfectSupportedWaldhausen T.ι) :=
  originalPrespectrumMap (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι)
    (perfectSupportedWaldhausen T.ι)
    ((perfectSupportedUnionToAcyclic_exact j T).comp
      (Fibration.acyclicInclusion_exact (perfectSupportedOpenNested j T))) rfl

/-- The flattening square is an equality of actual prespectrum maps, not just K-maps. -/
theorem perfectSupportedUnionToAcyclicPrespectrumMap_inclusion :
    perfectSupportedUnionToAcyclicPrespectrumMap j T ≫
      Fibration.acyclicInclusionPrespectrumMap (perfectSupportedOpenNested j T) =
        perfectSupportedUnionInclusionPrespectrumMap j T := by
  exact (originalPrespectrumMap_comp (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι)
    (Fibration.acyclicStructure (perfectSupportedOpenNested j T))
    (perfectSupportedWaldhausen T.ι)
    (perfectSupportedUnionToAcyclic_exact j T)
    (Fibration.acyclicInclusion_exact (perfectSupportedOpenNested j T)) rfl rfl).symm

/-- Canonical rebasing retains the original supported inclusion up to coherent homotopy. -/
def perfectSupportedUnionInclusionPrespectrumRebaseHomotopy :
    LoopPrespectrum.Homotopy
      (exactOriginalPrespectrumMap (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι)
        (perfectSupportedWaldhausen T.ι)
        ((perfectSupportedUnionToAcyclic_exact j T).comp
      (Fibration.acyclicInclusion_exact (perfectSupportedOpenNested j T))))
      (perfectSupportedUnionInclusionPrespectrumMap j T) :=
  exactOriginalPrespectrumMapChosenZeroHomotopy _ _ ((perfectSupportedUnionToAcyclic_exact j T).comp
      (Fibration.acyclicInclusion_exact (perfectSupportedOpenNested j T))) rfl

/-- Canonical rebasing likewise retains the actual supported-to-acyclic transport. -/
def perfectSupportedUnionToAcyclicPrespectrumRebaseHomotopy :
    LoopPrespectrum.Homotopy
      (exactOriginalPrespectrumMap (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι)
        (Fibration.acyclicStructure (perfectSupportedOpenNested j T))
          (perfectSupportedUnionToAcyclic_exact j T))
      (perfectSupportedUnionToAcyclicPrespectrumMap j T) :=
  exactOriginalPrespectrumMapChosenZeroHomotopy _ _ (perfectSupportedUnionToAcyclic_exact j T) rfl

/-- The supported nullhomotopy is the original whole acyclic nullhomotopy precomposed. -/
def perfectSupportedUnionPrespectrumNullhomotopy : LoopPrespectrum.Homotopy
    (perfectSupportedUnionInclusionPrespectrumMap j T ≫
      Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T))
    (zeroHom (perfectSupportedUnionPrespectrum j T) (perfectSupportedOpenPrespectrum j T)) := by
  have H := (Fibration.acyclicPrespectrumNullhomotopy (perfectSupportedOpenNested j T)).precomp
    (perfectSupportedUnionToAcyclicPrespectrumMap j T)
  exact {
    level := H.level
    at_zero n x := by
      simpa only [← Category.assoc, perfectSupportedUnionToAcyclicPrespectrumMap_inclusion]
        using H.at_zero n x
    at_one := H.at_one
    at_point := H.at_point
    comm := H.comm }

/-- Every point of the original nullhomotopy is retained, with the same time parameter. -/
theorem perfectSupportedUnionPrespectrumNullhomotopy_level (n : ℕ)
    (s : unitInterval) (x : (perfectSupportedUnionPrespectrum j T).space n) :
    (perfectSupportedUnionPrespectrumNullhomotopy j T).level n (s, x) =
      (Fibration.acyclicPrespectrumNullhomotopy (perfectSupportedOpenNested j T)).level n
        (s, (perfectSupportedUnionToAcyclicPrespectrumMap j T).map n x) := rfl

/-- Actual transport of the original canonical acyclic comparison into the coarse fiber. -/
def perfectSupportedUnionFiberPrespectrumMap : perfectSupportedUnionPrespectrum j T ⟶
    homotopyFiber (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T)) :=
  perfectSupportedUnionToAcyclicPrespectrumMap j T ≫
    Fibration.canonicalFiberPrespectrumMap (perfectSupportedOpenNested j T)

/-- Its source coordinate is literally the actual supported inclusion. -/
theorem perfectSupportedUnionFiberPrespectrumMap_projection :
    perfectSupportedUnionFiberPrespectrumMap j T ≫
      homotopyFiberProjection (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j
        T)) =
        perfectSupportedUnionInclusionPrespectrumMap j T := by
  rw [perfectSupportedUnionFiberPrespectrumMap, Category.assoc,
    Fibration.canonicalFiberPrespectrumMap_projection,
    perfectSupportedUnionToAcyclicPrespectrumMap_inclusion]

/-- Its entire fiber path is the specified original nullhomotopy, with no replacement. -/
theorem perfectSupportedUnionFiberPrespectrumMap_path (n : ℕ)
    (x : (perfectSupportedUnionPrespectrum j T).space n) (s : unitInterval) :
    ((perfectSupportedUnionFiberPrespectrumMap j T).map n x).1.2 s =
      (perfectSupportedUnionPrespectrumNullhomotopy j T).level n (s, x) := rfl

/-- Transport equals the actual path-space lift of that supported inclusion and nullhomotopy. -/
theorem perfectSupportedUnionFiberPrespectrumMap_eq_lift :
    perfectSupportedUnionFiberPrespectrumMap j T =
      homotopyFiberLift (Fibration.changeWeakPrespectrumMap (perfectSupportedOpenNested j T))
        (perfectSupportedUnionInclusionPrespectrumMap j T)
        (perfectSupportedUnionPrespectrumNullhomotopy j T) := by
  apply LoopPrespectrum.Hom.ext
  funext n
  ext x : 1
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun f ↦ f.map n x)
      (perfectSupportedUnionToAcyclicPrespectrumMap_inclusion j T)
  · rfl

/-- Both independent parameters commute with the unchanged original structure maps. -/
theorem perfectSupportedUnionPrespectrumNullhomotopy_structure (n : ℕ)
    (s t : unitInterval) (x : (perfectSupportedUnionPrespectrum j T).space n) :
    (perfectSupportedUnionPrespectrumNullhomotopy j T).level (n + 1)
        (s, (perfectSupportedUnionPrespectrum j T).structureMap n x t) =
      (perfectSupportedOpenPrespectrum j T).structureMap n
        ((perfectSupportedUnionPrespectrumNullhomotopy j T).level n (s, x)) t :=
  (perfectSupportedUnionPrespectrumNullhomotopy j T).comm n s x t

/-- The actual supported fiber map is a stable equivalence in every integer degree. -/
theorem perfectSupportedUnionFiberPrespectrumMap_isStableEquivalence :
    IsStableEquivalence (perfectSupportedUnionFiberPrespectrumMap j T) := by
  apply IsStableEquivalence.comp ?_
    (perfectSupportedOpen_canonicalFiberPrespectrumMap_isStableEquivalence j T)
  intro d
  change IsIso ((stableHomotopyFunctor d).map (perfectSupportedUnionAcyclicPrespectrumIso j T).hom)
  infer_instance

/-- Stable supported inclusion retains the existing canonical supported K-map. -/
theorem perfectSupportedUnionInclusionPrespectrumMap_naturality (n : ℕ)
    (a : PerfectSupportedK (T ⊔ j.opensRange).ι n) :
    originalKStableEquiv (perfectSupportedWaldhausen T.ι) n
        (Additive.ofMul (perfectSupportedUnionKMap j T n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (perfectSupportedUnionInclusionPrespectrumMap j T)
        (originalKStableEquiv (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι) n (Additive.ofMul
          a)) :=
  originalKStableEquiv_naturality _ _ ((perfectSupportedUnionToAcyclic_exact j T).comp
      (Fibration.acyclicInclusion_exact (perfectSupportedOpenNested j T))) rfl n a

attribute [colib_tag "COL-0335",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Support.lean:184-218"
    "comparison" "The supported union/acyclic flattening extends to actual prespectra"]
  perfectSupportedUnionAcyclicPrespectrumIso
  perfectSupportedUnionToAcyclicPrespectrumMap_inclusion

attribute [colib_tag "COL-0335",
  colib_ref "Waldhausen1985" "Section 1.6, Theorem 1.6.4 and proof, pp. 350-352" "adaptation"
    "The original acyclic-to-coarse-fiber comparison transported through native support"]
  perfectSupportedUnionFiberPrespectrumMap_isStableEquivalence
  perfectSupportedUnionFiberPrespectrumMap_projection
  perfectSupportedUnionFiberPrespectrumMap_path
  perfectSupportedUnionFiberPrespectrumMap_eq_lift
  perfectSupportedUnionPrespectrumNullhomotopy_structure
  perfectSupportedUnionInclusionPrespectrumMap_naturality

end AlgebraicGeometry.Scheme.Modules
