/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability

/-!
# Normality of relative normalization in an integral normal source

The affine charts of the relative normalization are integral closures in rings of sections
of the source. The native normal-global-sections theorem and Tag 034L give their normality.
This integral-source argument does not require a decomposition into connected components.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Relative normalization in an integral normal source is normal. -/
theorem isNormal_normalization_of_integral_source {X Y : Scheme.{u}}
    [IsIntegral X] [IsNormal X] (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    IsNormal f.normalization := by
  apply isNormal_of_openCover f.normalizationOpenCover
  intro U
  let := (f.app U.1).hom.toAlgebra
  change IsNormal (Spec (.of (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))))
  let V := f ⁻¹ᵁ U.1
  by_cases hV : Nonempty V
  · have : Nonempty V.toScheme := hV
    have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
    have : IsNormal V.toScheme := by
      refine (isNormal_iff_stalk_normal _).mpr fun x => ?_
      have : IsIntegrallyClosed (X.presheaf.stalk x.1) := IsNormal.stalk_normal _
      exact ⟨inferInstance, IsIntegrallyClosed.of_equiv
        (V.stalkIso x).commRingCatIsoToRingEquiv.symm⟩
    have : IsIntegrallyClosed Γ(V.toScheme, ⊤) := normal_globalSections V.toScheme
    have : IsIntegrallyClosed Γ(X, V) :=
      IsIntegrallyClosed.of_equiv V.topIso.commRingCatIsoToRingEquiv
    have : IsNormalDomain Γ(X, V) := ⟨inferInstance, inferInstance⟩
    have := integralClosure_isNormalDomain (R := Γ(Y, U.1))
      (S := Γ(X, V)) inferInstance
    exact isNormal_spec_iff.mpr (IsNormalRing.of_isIntegrallyClosed _)
  · have hbot : V = ⊥ := by
      ext x
      exact ⟨fun hx => (hV ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    have : Subsingleton Γ(X, V) := by rw [hbot]; infer_instance
    have : Subsingleton (integralClosure Γ(Y, U.1) Γ(X, V)) := inferInstance
    refine isNormal_spec_iff.mpr fun p hp => ?_
    exact (hp.ne_top (Subsingleton.elim _ _)).elim

end AlgebraicGeometry.Scheme.Hom
