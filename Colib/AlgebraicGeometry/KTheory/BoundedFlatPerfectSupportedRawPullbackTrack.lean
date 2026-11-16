/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedPullback
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportHomotopy
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentParameterCoordinate
public import Colib.AlgebraicGeometry.Scheme.QuasiCompactOpenPairPolynomialZeroSection
public import Colib.CategoryTheory.Functor.IdentityAutomorphism

/-!
# The original Laurent scalar on global supported prespectra

The actual geometric pullback of an open pair carries the forward Laurent coordinate on its
original supported complexes. Realizing its natural automorphism gives a homotopy on the actual
iterated-S maps, before any localization or restriction to an affine chart.
-/
@[expose] public noncomputable section

open CategoryTheory Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum

universe u

namespace AlgebraicGeometry.Scheme.Modules

open Scheme.Bass
open Scheme.PolynomialLaurent.GlobalIndex

variable {A B : Scheme.OpenPairs.{u}}

/-- The original iterated-S map of actual, not necessarily flat, geometric pair pullback. -/
def boundedAboveFlatPerfectSupportedPullbackPrespectrumMap (p : A ⟶ B) :=
  exactOriginalPrespectrumMap (boundedAboveFlatPerfectSupportedWaldhausen B.hom)
    (boundedAboveFlatPerfectSupportedWaldhausen A.hom)
    (boundedAboveFlatPerfectSupportedPullback_isExact p)

/-- The given forward scalar acts on the original geometric pullback functor. -/
def boundedAboveFlatPerfectSupportedPullbackUnitIso (p : A ⟶ B) (r : (Γ(A.right, ⊤))ˣ) :
    boundedAboveFlatPerfectSupportedPullback p ≅ boundedAboveFlatPerfectSupportedPullback p :=
  Functor.IdentityAutomorphism.onFunctor (boundedAboveFlatPerfectSupportedPullback p)
    (boundedAboveFlatPerfectSupportedGlobalUnitIso A.hom r)

/-- Forgetting support preserves the forward scalar on the actual pullback complex. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedRawStep.lean:82-89"
  "adaptation" "The original supported pullback retains its forward scalar component."]
theorem boundedAboveFlatPerfectSupportedPullbackUnitIso_hom_original (p : A ⟶ B)
    (r : (Γ(A.right, ⊤))ˣ) (K : (boundedAboveFlatPerfectSupported B.hom).FullSubcategory) :
    (boundedAboveFlatPerfectSupported A.hom).ι.map
        ((boundedAboveFlatPerfectSupportedPullbackUnitIso p r).hom.app K) =
      (complexGlobalUnitIso A.right r).hom.app
        ((boundedAboveFlatPerfectSupportedPullback p).obj K).obj := by
  simp only [boundedAboveFlatPerfectSupportedPullbackUnitIso,
    Functor.IdentityAutomorphism.onFunctor_hom_app, boundedAboveFlatPerfectSupportedGlobalUnitIso,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, ObjectProperty.ι_obj, Functor.id_obj]

/-- The whole original scalar track before localization, not merely its induced map on K-groups. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedRawStep.lean:93-97"
  "adaptation" "Realize the original supported scalar automorphism on actual pullback."]
def boundedAboveFlatPerfectSupportedPullbackUnitHomotopy (p : A ⟶ B) (r : (Γ(A.right, ⊤))ˣ) :
    Homotopy (boundedAboveFlatPerfectSupportedPullbackPrespectrumMap p)
      (boundedAboveFlatPerfectSupportedPullbackPrespectrumMap p) :=
  exactOriginalPrespectrumIsoHomotopy _ _ (boundedAboveFlatPerfectSupportedPullback_isExact p)
    (boundedAboveFlatPerfectSupportedPullback_isExact p)
    (boundedAboveFlatPerfectSupportedPullbackUnitIso p r)

/-- The forward coordinate of the actual integer Laurent product of an arbitrary qc open pair. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedRawStep.lean:99-103"
  "adaptation" "Keep the original forward Laurent coordinate for every quasi-compact open pair."]
def boundedAboveFlatPerfectSupportedLaurentProjectionUnitHomotopy
    (A : Scheme.QuasiCompactOpenPairs.{u}) :
    Homotopy
      (boundedAboveFlatPerfectSupportedPullbackPrespectrumMap (pairLaurentProjection.app A).hom)
      (boundedAboveFlatPerfectSupportedPullbackPrespectrumMap (pairLaurentProjection.app A).hom) :=
  boundedAboveFlatPerfectSupportedPullbackUnitHomotopy (pairLaurentProjection.app A).hom
    (laurentScalar (op A.obj.right))

end AlgebraicGeometry.Scheme.Modules
