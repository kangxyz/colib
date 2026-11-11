/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectTensorUnitSupport
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectSupport
public import Colib.KTheory.Waldhausen.Iterated.ExactPastingHomotopy

/-!
# The original supported tensor-unit prism

The inherited Waldhausen structure retains the actual open-restriction acyclicity property.
The tensor-unit unitor square gives a whole relative comparison of original iterated-S tracks
on this supported category, with canonical zero rebasing and the original endpoint maps.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Actual unit tensor preserves the inherited supported Waldhausen structure. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportHomotopy.lean:29"
  "adaptation" "Original tensor/unitor restricted to the actual supported full subcategory."]
theorem boundedAboveFlatPerfectSupportedTensorUnit_exact :
    CategoryTheory.Waldhausen.IsExact (boundedAboveFlatPerfectSupportedWaldhausen j).cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).weq
      (boundedAboveFlatPerfectSupportedWaldhausen j).cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).weq
      (boundedAboveFlatPerfectSupportedTensorUnit j) :=
  (CategoryTheory.Waldhausen.IsExact.id _ _).of_iso
    (boundedAboveFlatPerfectSupportedTensorUnitIso j).symm

/-- The original supported tensor automorphism fixes the chosen zero before rebasing. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportHomotopy.lean:37"
  "adaptation" "Original tensor/unitor restricted to the actual supported full subcategory."]
theorem boundedAboveFlatPerfectSupportedTensorUnitAutomorphism_zero (r : (Γ(X, ⊤))ˣ) :
    (boundedAboveFlatPerfectSupportedTensorUnitAutomorphism j r).hom.app
        (boundedAboveFlatPerfectSupportedWaldhausen j).zero = 𝟙 _ :=
  ((boundedAboveFlatPerfectSupportedTensorUnit_exact j).zero
    (boundedAboveFlatPerfectSupportedWaldhausen j).isZero).eq_of_src _ _

/-- The normalized original prespectrum map of supported unit tensor. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportHomotopy.lean:44"
  "adaptation" "Original tensor/unitor restricted to the actual supported full subcategory."]
def boundedAboveFlatPerfectSupportedTensorUnitPrespectrumMap :=
  exactOriginalPrespectrumMap (boundedAboveFlatPerfectSupportedWaldhausen j)
    (boundedAboveFlatPerfectSupportedWaldhausen j)
    (boundedAboveFlatPerfectSupportedTensorUnit_exact j)

/-- The original supported identity functor retains its canonical zero normalization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportHomotopy.lean:49"
  "adaptation" "Original tensor/unitor restricted to the actual supported full subcategory."]
def boundedAboveFlatPerfectSupportedIdentityPrespectrumMap :=
  exactOriginalPrespectrumMap (boundedAboveFlatPerfectSupportedWaldhausen j)
    (boundedAboveFlatPerfectSupportedWaldhausen j) (CategoryTheory.Waldhausen.IsExact.id _ _)

/-- The full original iterated-S loop of the supported coefficient tensor action. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportHomotopy.lean:54"
  "adaptation" "Original tensor/unitor restricted to the actual supported full subcategory."]
def boundedAboveFlatPerfectSupportedTensorUnitHomotopy (r : (Γ(X, ⊤))ˣ) :
    Homotopy (boundedAboveFlatPerfectSupportedTensorUnitPrespectrumMap j)
      (boundedAboveFlatPerfectSupportedTensorUnitPrespectrumMap j) :=
  exactOriginalPrespectrumIsoHomotopy _ _ (boundedAboveFlatPerfectSupportedTensorUnit_exact j)
    (boundedAboveFlatPerfectSupportedTensorUnit_exact j)
    (boundedAboveFlatPerfectSupportedTensorUnitAutomorphism j r)

/-- The full original supported scalar loop, before any stable-localization quotient. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportHomotopy.lean:62"
  "adaptation" "Original tensor/unitor restricted to the actual supported full subcategory."]
def boundedAboveFlatPerfectSupportedGlobalUnitHomotopy (r : (Γ(X, ⊤))ˣ) :
    Homotopy (boundedAboveFlatPerfectSupportedIdentityPrespectrumMap j)
      (boundedAboveFlatPerfectSupportedIdentityPrespectrumMap j) :=
  exactOriginalPrespectrumIsoHomotopy _ _ (CategoryTheory.Waldhausen.IsExact.id _ _)
    (CategoryTheory.Waldhausen.IsExact.id _ _) (boundedAboveFlatPerfectSupportedGlobalUnitIso j r)

/-- The genuine supported tensor unitor gives the original coherent spectrum comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportHomotopy.lean:69"
  "adaptation" "Original tensor/unitor restricted to the actual supported full subcategory."]
def boundedAboveFlatPerfectSupportedTensorUnitUnitorHomotopy :
    Homotopy (boundedAboveFlatPerfectSupportedTensorUnitPrespectrumMap j)
      (boundedAboveFlatPerfectSupportedIdentityPrespectrumMap j) :=
  exactOriginalPrespectrumIsoHomotopy _ _ (boundedAboveFlatPerfectSupportedTensorUnit_exact j)
    (CategoryTheory.Waldhausen.IsExact.id _ _) (boundedAboveFlatPerfectSupportedTensorUnitIso j)

/-- The unchanged supported tensor/scalar square supplies the whole relative iterated-S prism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportHomotopy.lean:76"
  "adaptation" "Original tensor/unitor restricted to the actual supported full subcategory."]
def boundedAboveFlatPerfectSupportedTensorUnitUnitorPasting (r : (Γ(X, ⊤))ˣ) :
    ((boundedAboveFlatPerfectSupportedTensorUnitHomotopy j r).trans
      (boundedAboveFlatPerfectSupportedTensorUnitUnitorHomotopy j)).RelHomotopy
      ((boundedAboveFlatPerfectSupportedTensorUnitUnitorHomotopy j).trans
        (boundedAboveFlatPerfectSupportedGlobalUnitHomotopy j r)) :=
  exactOriginalPrespectrumPastingHomotopy _ _
    (boundedAboveFlatPerfectSupportedTensorUnit_exact j)
    (boundedAboveFlatPerfectSupportedTensorUnit_exact j)
    (CategoryTheory.Waldhausen.IsExact.id _ _) (CategoryTheory.Waldhausen.IsExact.id _ _)
    (boundedAboveFlatPerfectSupportedTensorUnitAutomorphism j r).hom
    (boundedAboveFlatPerfectSupportedTensorUnitIso j).hom
    (boundedAboveFlatPerfectSupportedTensorUnitIso j).hom
    (boundedAboveFlatPerfectSupportedGlobalUnitIso j r).hom
    (fun _ ↦ (boundedAboveFlatPerfectSupportedWaldhausen j).weq_iso _ inferInstance)
    (fun _ ↦ (boundedAboveFlatPerfectSupportedWaldhausen j).weq_iso _ inferInstance)
    (fun _ ↦ (boundedAboveFlatPerfectSupportedWaldhausen j).weq_iso _ inferInstance)
    (fun _ ↦ (boundedAboveFlatPerfectSupportedWaldhausen j).weq_iso _ inferInstance)
    (boundedAboveFlatPerfectSupportedTensorUnitAutomorphism_unitor j r)

end AlgebraicGeometry.Scheme.Modules
