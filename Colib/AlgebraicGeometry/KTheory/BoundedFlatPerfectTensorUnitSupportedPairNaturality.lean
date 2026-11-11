/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedForgetNaturality
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedPullback

/-! # Supported tensor input along the original geometric pair square

The actual supported pullback preserves the original restriction-acyclicity
predicate. Forgetting it intertwines its tensor-unit automorphism with the
original ambient tensor pullback through the displayed underlying isomorphism.
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
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)

/-- Original supported pair pullback followed by the actual supported tensor functor. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedPairNaturality.lean:29"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
def tensorSupportedPairFunctor :=
  boundedAboveFlatPerfectSupportedPullback p ⋙ boundedAboveFlatPerfectSupportedTensorUnit A.hom

/-- The actual pair restriction and supported tensor retain their inherited exact structures. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedPairNaturality.lean:33"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
theorem tensorSupportedPair_exact :
    IsExact (boundedAboveFlatPerfectSupportedWaldhausen B.hom).cof
      (boundedAboveFlatPerfectSupportedWaldhausen B.hom).weq
      (boundedAboveFlatPerfectSupportedWaldhausen A.hom).cof
      (boundedAboveFlatPerfectSupportedWaldhausen A.hom).weq (tensorSupportedPairFunctor p) :=
  (boundedAboveFlatPerfectSupportedPullback_isExact p).comp
    (boundedAboveFlatPerfectSupportedTensorUnit_exact A.hom)

/-- The original forward unit acts on every genuinely supported pulled-back complex. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedPairNaturality.lean:42"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
def tensorSupportedPairAutomorphism (r : (Γ(A.right, ⊤))ˣ) :
    tensorSupportedPairFunctor p ≅ tensorSupportedPairFunctor p :=
  Functor.isoWhiskerLeft (boundedAboveFlatPerfectSupportedPullback p)
    (boundedAboveFlatPerfectSupportedTensorUnitAutomorphism A.hom r)

/-- Forgetting the pair support retains the original geometric tensor pullback. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedPairNaturality.lean:48"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
def tensorSupportedPairForgetIso :
    tensorSupportedPairFunctor p ⋙ tensorCoefficientSupportedForget A.hom ≅
      tensorCoefficientSupportedForget B.hom ⋙
        boundedAboveFlatPerfectTensorUnitPullback p.right :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (by intro K L g; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

/-- The complete actual pair-forgetting square preserves the original tensor coefficient. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedPairNaturality.lean:56"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
theorem tensorSupportedPairForget_unit (r : (Γ(A.right, ⊤))ˣ) :
    Functor.whiskerRight (tensorSupportedPairAutomorphism p r).hom
        (tensorCoefficientSupportedForget A.hom) ≫ (tensorSupportedPairForgetIso p).hom =
      (tensorSupportedPairForgetIso p).hom ≫
        Functor.whiskerLeft (tensorCoefficientSupportedForget B.hom)
          (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism p.right r).hom := by
  apply NatTrans.ext
  funext K
  apply (boundedAboveFlatPerfectComplex A.right.toRingedSpace).ι.map_injective
  simp only [NatTrans.comp_app, tensorSupportedPairForgetIso, NatIso.ofComponents_hom_app,
    Iso.refl_hom, Category.id_comp, Category.comp_id, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, tensorSupportedPairAutomorphism, Functor.isoWhiskerLeft_hom,
    boundedAboveFlatPerfectTensorUnitPullbackAutomorphism]
  exact (boundedAboveFlatPerfectSupportedTensorUnitAutomorphism_hom_original A.hom r
    ((boundedAboveFlatPerfectSupportedPullback p).obj K)).trans
    (boundedAboveFlatPerfectTensorUnitAutomorphism_hom_original A.right r
      ((boundedAboveFlatPerfectPullback p.right).obj
        ((tensorCoefficientSupportedForget B.hom).obj K))).symm

/-- The actual geometric supported input square realizes to its whole normalization-relative prism.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedPairNaturality.lean:77"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
def tensorSupportedPairForgetPasting (r : (Γ(A.right, ⊤))ˣ) :=
  exactOriginalPrespectrumPastingHomotopy
    (boundedAboveFlatPerfectSupportedWaldhausen B.hom)
    (boundedAboveFlatPerfectWaldhausen A.right.toRingedSpace)
    ((tensorSupportedPair_exact p).comp (tensorCoefficientSupportedForget_exact A.hom))
    ((tensorSupportedPair_exact p).comp (tensorCoefficientSupportedForget_exact A.hom))
    ((tensorCoefficientSupportedForget_exact B.hom).comp
      (boundedAboveFlatPerfectTensorUnitPullback_exact p.right))
    ((tensorCoefficientSupportedForget_exact B.hom).comp
      (boundedAboveFlatPerfectTensorUnitPullback_exact p.right))
    (Functor.whiskerRight (tensorSupportedPairAutomorphism p r).hom
      (tensorCoefficientSupportedForget A.hom))
    (tensorSupportedPairForgetIso p).hom (tensorSupportedPairForgetIso p).hom
    (Functor.whiskerLeft (tensorCoefficientSupportedForget B.hom)
      (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism p.right r).hom)
    (fun _ => (boundedAboveFlatPerfectWaldhausen A.right.toRingedSpace).weq_iso _ inferInstance)
    (fun _ => (boundedAboveFlatPerfectWaldhausen A.right.toRingedSpace).weq_iso _ inferInstance)
    (fun _ => (boundedAboveFlatPerfectWaldhausen A.right.toRingedSpace).weq_iso _ inferInstance)
    (fun _ => (boundedAboveFlatPerfectWaldhausen A.right.toRingedSpace).weq_iso _ inferInstance)
    (tensorSupportedPairForget_unit p r)

end AlgebraicGeometry.Scheme.Modules
