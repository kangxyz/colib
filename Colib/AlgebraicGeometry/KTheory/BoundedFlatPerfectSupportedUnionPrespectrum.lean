/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedOpenFibration
public import Colib.KTheory.Waldhausen.Fibration.SpectrumComparison
public import Colib.KTheory.Waldhausen.Iterated.ChosenZeroCoherence
public import Colib.KTheory.Waldhausen.Iterated.StableFunctoriality

/-!
# Canonically rebased bounded-flat union-support fiber

The union-supported and relative-acyclic exact categories have independently chosen zeros.
The map below therefore uses canonical normalization, not an asserted equality of those zeros.
Its projection is coherently compared with the normalized literal inclusion, while its fiber
path is exactly the original acyclic nullhomotopy evaluated on the normalized source map.

This is a native spectrum extension of the exact equivalence and original canonical fiber
comparison in Quillen `BoundedFlat/SupportedOpenFibration.lean:64-293` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. No compactness assumption or Bass construction
is involved. With auxiliary open T, the support is the complement of T union the image of j.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology Topology.LoopPrespectrum
open scoped unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The exact inverse equivalence with its canonical chosen-zero normalization. -/
def boundedAboveFlatPerfectSupportedUnionToAcyclicPrespectrumMap :
    originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι) ⟶
      originalPrespectrum (Fibration.acyclicStructure
        (boundedAboveFlatPerfectSupportedOpenNested j T)) :=
  exactOriginalPrespectrumMap
    (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι)
    (Fibration.acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j T))
    (boundedAboveFlatPerfectSupportedUnionToAcyclic_exact j T)

/-- Canonical normalization of the literal union-support inclusion. -/
def boundedAboveFlatPerfectSupportedUnionInclusionPrespectrumMap :
    originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι) ⟶
      originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen T.ι) :=
  exactOriginalPrespectrumMap
    (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι)
    (boundedAboveFlatPerfectSupportedWaldhausen T.ι)
    (boundedAboveFlatPerfectSupportedUnionInclusion_isExact j T)

/-- The original canonical fiber map after the specified normalization of its source. -/
def boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap :
    originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι) ⟶
      homotopyFiber (Fibration.changeWeakPrespectrumMap
        (boundedAboveFlatPerfectSupportedOpenNested j T)) :=
  boundedAboveFlatPerfectSupportedUnionToAcyclicPrespectrumMap j T ≫
    Fibration.canonicalFiberPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j T)

/-- The projection retains the original acyclic inclusion after the same normalization. -/
theorem boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap_projection :
    boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap j T ≫
        homotopyFiberProjection (Fibration.changeWeakPrespectrumMap
          (boundedAboveFlatPerfectSupportedOpenNested j T)) =
      boundedAboveFlatPerfectSupportedUnionToAcyclicPrespectrumMap j T ≫
        Fibration.acyclicInclusionPrespectrumMap
          (boundedAboveFlatPerfectSupportedOpenNested j T) := by
  rw [boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap, Category.assoc,
    Fibration.canonicalFiberPrespectrumMap_projection]

/-- Every fiber coordinate keeps the entire original acyclic path, not only its endpoints. -/
theorem boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap_path (n : ℕ)
    (x : (originalPrespectrum
      (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι)).space n)
    (s : unitInterval) :
    ((boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap j T).map n x).1.2 s =
      (Fibration.acyclicPrespectrumNullhomotopy
        (boundedAboveFlatPerfectSupportedOpenNested j T)).level n
          (s, (boundedAboveFlatPerfectSupportedUnionToAcyclicPrespectrumMap j T).map n x) := rfl

/-- The complete coherent projection track compares with the normalized literal inclusion.
Only the inherited zero of the acyclic inclusion is strict; the union zero is not identified. -/
def boundedAboveFlatPerfectSupportedUnionProjectionHomotopy :
    LoopPrespectrum.Homotopy
      (boundedAboveFlatPerfectSupportedUnionToAcyclicPrespectrumMap j T ≫
        Fibration.acyclicInclusionPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j T))
      (boundedAboveFlatPerfectSupportedUnionInclusionPrespectrumMap j T) :=
  ((exactOriginalPrespectrumMapChosenZeroHomotopy
      (Fibration.acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j T))
      (boundedAboveFlatPerfectSupportedWaldhausen T.ι)
      (Fibration.acyclicInclusion_exact (boundedAboveFlatPerfectSupportedOpenNested j T))
      rfl).symm.precomp (boundedAboveFlatPerfectSupportedUnionToAcyclicPrespectrumMap j T)).trans
    (exactOriginalPrespectrumMapCompHomotopy
      (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι)
      (Fibration.acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j T))
      (boundedAboveFlatPerfectSupportedWaldhausen T.ι)
      (boundedAboveFlatPerfectSupportedUnionToAcyclic_exact j T)
      (Fibration.acyclicInclusion_exact
        (boundedAboveFlatPerfectSupportedOpenNested j T))).symm

/-- The original whole null path transported along the normalized inverse equivalence. -/
def boundedAboveFlatPerfectSupportedUnionRebasedNullhomotopy :
    LoopPrespectrum.Homotopy
      ((boundedAboveFlatPerfectSupportedUnionToAcyclicPrespectrumMap j T ≫
        Fibration.acyclicInclusionPrespectrumMap
          (boundedAboveFlatPerfectSupportedOpenNested j T)) ≫
        Fibration.changeWeakPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j T))
      (zeroHom
        (originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι))
        (originalPrespectrum (boundedAboveFlatPerfectSupportedOpenWaldhausen j T))) := by
  let H := LoopPrespectrum.Homotopy.precomp
    (boundedAboveFlatPerfectSupportedUnionToAcyclicPrespectrumMap j T)
    (Fibration.acyclicPrespectrumNullhomotopy (boundedAboveFlatPerfectSupportedOpenNested j T))
  exact {
    level := H.level
    at_zero := H.at_zero
    at_one := H.at_one
    at_point := H.at_point
    comm := H.comm }

/-- A nullhomotopy for the direct normalized inclusion, with the projection track retained.
This concatenated path is not asserted equal to the original fiber coordinate path. -/
def boundedAboveFlatPerfectSupportedUnionInclusionNullhomotopy :
    LoopPrespectrum.Homotopy
      (boundedAboveFlatPerfectSupportedUnionInclusionPrespectrumMap j T ≫
        Fibration.changeWeakPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j T))
      (zeroHom
        (originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι))
        (originalPrespectrum (boundedAboveFlatPerfectSupportedOpenWaldhausen j T))) :=
  ((boundedAboveFlatPerfectSupportedUnionProjectionHomotopy j T).symm.postcomp
    (Fibration.changeWeakPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j T))).trans
      (boundedAboveFlatPerfectSupportedUnionRebasedNullhomotopy j T)

/-- The normalized inverse equivalence is stable in every integer degree, including zero. -/
theorem boundedAboveFlatPerfectSupportedUnionToAcyclicPrespectrumMap_isStableEquivalence :
    IsStableEquivalence (boundedAboveFlatPerfectSupportedUnionToAcyclicPrespectrumMap j T) := by
  apply (exactOriginalPrespectrumMap_isStableEquivalence_iff
    (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι)
    (Fibration.acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j T))
    (boundedAboveFlatPerfectSupportedUnionToAcyclic_exact j T)).2
  intro n
  exact (boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T n).symm.bijective

/-- Normalization induces the original inverse K-map, rather than a replacement K-map. -/
theorem boundedAboveFlatPerfectSupportedUnionToAcyclicPrespectrumMap_K_naturality
    (n : ℕ) (a : BoundedAboveFlatPerfectSupportedK (T ⊔ j.opensRange).ι n) :
    originalKStableEquiv
        (Fibration.acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j T)) n
        (Additive.ofMul
          ((boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T n).symm a)) =
      (stableHomotopyFunctor (n : ℤ)).map
        (boundedAboveFlatPerfectSupportedUnionToAcyclicPrespectrumMap j T)
        (originalKStableEquiv
          (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι) n
          (Additive.ofMul a)) :=
  originalKStableEquiv_exact_naturality
    (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι)
    (Fibration.acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j T))
    (boundedAboveFlatPerfectSupportedUnionToAcyclic_exact j T) n a

/-- The actual canonical coarse fiber comparison remains stable after source normalization. -/
@[colib_tag "COL-0506",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenFibration.lean:213-284"
    "ingredient"
    "Exact K-equivalence and original fiber comparison; native normalized spectrum extension"]
theorem boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap_isStableEquivalence :
    IsStableEquivalence (boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap j T) :=
  (boundedAboveFlatPerfectSupportedUnionToAcyclicPrespectrumMap_isStableEquivalence j T).comp
    (Fibration.canonicalFiberPrespectrumMap_isStableEquivalence_of_weak
      (boundedAboveFlatPerfectSupportedOpenNested j T)
      (boundedAboveFlatPerfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T))

end AlgebraicGeometry.Scheme.Modules
