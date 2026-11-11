/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientInputNaturality
public import Colib.KTheory.Waldhausen.Iterated.NormalizationTrackPasting

/-! # Actual normalization of the tensor cell on supported inputs

The original composite exact functor and the two separately normalized maps are
related by their real binary normalization track. The complete tensor-unit loop
commutes with that track by the existing normalization prism, at every spectrum
level and with both homotopy times intact.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
  (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

/-- The original supported input map before the actual tensor coefficient operation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedInputNormalization\
    .lean:31"
  "adaptation" "Original supported input double cylinder and whole binary normalization prism."]
def tensorSupportedInputPrespectrumMap :=
  exactOriginalPrespectrumMap (boundedAboveFlatPerfectSupportedWaldhausen j)
    (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace) (tensorCoefficientSupportedForget_exact j)

/-- Tensor pullback on original supported inputs, with a single canonical composite rebase. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedInputNormalization\
    .lean:36"
  "adaptation" "Original supported input double cylinder and whole binary normalization prism."]
def tensorSupportedCompositePrespectrumMap :=
  exactOriginalPrespectrumMap (boundedAboveFlatPerfectSupportedWaldhausen j)
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
    ((tensorCoefficientSupportedForget_exact j).comp
      (boundedAboveFlatPerfectTensorUnitPullback_exact f))

/-- The original automorphism on the true composite exact functor. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedInputNormalization\
    .lean:42"
  "adaptation" "Original supported input double cylinder and whole binary normalization prism."]
def tensorSupportedCompositeHomotopy :
    Homotopy (tensorSupportedCompositePrespectrumMap j f)
      (tensorSupportedCompositePrespectrumMap j f) :=
  exactOriginalPrespectrumHomotopy _ _
    ((tensorCoefficientSupportedForget_exact j).comp
      (boundedAboveFlatPerfectTensorUnitPullback_exact f))
    ((tensorCoefficientSupportedForget_exact j).comp
      (boundedAboveFlatPerfectTensorUnitPullback_exact f))
    (Functor.whiskerLeft (tensorCoefficientSupportedForget j)
      (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom)
    (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)

/-- The actual binary normalization, rather than an asserted strict composition equality. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedInputNormalization\
    .lean:53"
  "adaptation" "Original supported input double cylinder and whole binary normalization prism."]
def tensorSupportedInputNormalization :
    Homotopy (tensorSupportedCompositePrespectrumMap j f)
      (tensorSupportedInputPrespectrumMap j ≫ boundedAboveFlatPerfectTensorUnitPrespectrumMap f) :=
  exactOriginalPrespectrumMapCompHomotopy _ _ _
    (tensorCoefficientSupportedForget_exact j) (boundedAboveFlatPerfectTensorUnitPullback_exact f)

/-- Original supported input naturality is a whole normalization-relative spectrum prism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedInputNormalization\
    .lean:60"
  "adaptation" "Original supported input double cylinder and whole binary normalization prism."]
def tensorSupportedInputNormalizationPasting :
    ((tensorSupportedCompositeHomotopy j f r).trans
      (tensorSupportedInputNormalization j f)).RelHomotopy
      ((tensorSupportedInputNormalization j f).trans
        (Homotopy.precomp (tensorSupportedInputPrespectrumMap j)
          (boundedAboveFlatPerfectTensorUnitHomotopy f r))) :=
  exactNormalizationRightTrackPasting (tensorCoefficientSupportedForget_exact j)
    (boundedAboveFlatPerfectTensorUnitPullback_exact f)
    (boundedAboveFlatPerfectTensorUnitPullback_exact f)
    (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom
    (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)

/-- The same complete prism after the original ordinary loop-tail stabilization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedInputNormalization\
    .lean:72"
  "adaptation" "Original supported input double cylinder and whole binary normalization prism."]
def tensorSupportedInputStabilizedPasting :=
  (tensorSupportedInputNormalizationPasting j f r).postcomp
    (stabilizationMap (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))

end AlgebraicGeometry.Scheme.Modules
