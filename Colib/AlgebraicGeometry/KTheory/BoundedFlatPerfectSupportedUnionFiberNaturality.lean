/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedPullbackPrespectrum
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedUnionPrespectrum

/-!
# The original union-supported fiber square

The original union-support functor and inverse flattening commute before normalization.
Composition and chosen-zero tracks transport this square to the actual canonical fiber.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS Topology Topology.LoopPrespectrum

universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.right = g ≫ j)

/-- The full fiber square retains the original union-support pullback and both chosen zeros. -/
@[colib_tag "COL-0385",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenNaturality.lean:75-99"
    "ingredient"
    "Union-support boundary square extended by native composition and chosen-zero tracks"]
def boundedAboveFlatPerfectSupportedUnionFiberPullbackHomotopy :
    LoopPrespectrum.Homotopy
      (boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap j T ≫
        boundedAboveFlatPerfectSupportedFiberPullbackPrespectrumMap j' j f g w)
      (exactOriginalPrespectrumMap
          (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι)
          (boundedAboveFlatPerfectSupportedWaldhausen (S ⊔ j'.opensRange).ι)
          (boundedAboveFlatPerfectSupportedPullback_isExact
            (supportedPairUnionSquare j' j f g w)) ≫
        boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap j' S) := by
  let N := boundedAboveFlatPerfectSupportedOpenNested j T
  let M := boundedAboveFlatPerfectSupportedOpenNested j' S
  let V := boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι
  let W := boundedAboveFlatPerfectSupportedWaldhausen (S ⊔ j'.opensRange).ι
  let hF := boundedAboveFlatPerfectSupportedPullback_isExact f
  let hFc := boundedAboveFlatPerfectSupportedOpenPullback_isExact j' j f g w
  let hFc' := boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w
  let hA := acyclicFunctor_exact N M hF hFc
  let hA' := acyclicFunctor_exact N M hF.rebase hFc'
  let hP := boundedAboveFlatPerfectSupportedUnionToAcyclic_exact j T
  let hQ := boundedAboveFlatPerfectSupportedUnionToAcyclic_exact j' S
  let hU := boundedAboveFlatPerfectSupportedPullback_isExact
    (supportedPairUnionSquare j' j f g w)
  let h0 := acyclicFunctor_zero N M hFc'
    (boundedAboveFlatPerfectSupportedPullbackNormalized_zero f)
  let e := acyclicFunctorIso N M hFc hFc'
    (boundedAboveFlatPerfectSupportedPullbackNormalizationIso f)
  let H := (exactOriginalPrespectrumIsoHomotopy (acyclicStructure N) (acyclicStructure M)
    hA hA' e).trans
      (exactOriginalPrespectrumMapChosenZeroHomotopy (acyclicStructure N)
        (acyclicStructure M) hA' h0)
  let J := (H.symm.precomp (exactOriginalPrespectrumMap V (acyclicStructure N) hP)).trans
    (exactOriginalPrespectrumMapCompHomotopy V (acyclicStructure N)
      (acyclicStructure M) hP hA).symm
  let K := J.trans (exactOriginalPrespectrumMapCompHomotopy V W (acyclicStructure M) hU hQ)
  rw [boundedAboveFlatPerfectSupportedUnionFiberPrespectrumRebasedMap, Category.assoc,
    boundedAboveFlatPerfectSupportedCanonicalFiberPrespectrumMap_pullback]
  exact K.postcomp (canonicalFiberPrespectrumMap M)

end AlgebraicGeometry.Scheme.Modules
