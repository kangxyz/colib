/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterNegativeSign
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterCurrentNegativeBoundaryCorrection

/-!
# Every original negative boundary agrees with the intrinsic current boundary

The genuine ambient and supported finite corrections are identities in all
indices. The already established intrinsic boundary correction square therefore
identifies the existing current boundary with the existing original signed
negative boundary. No boundary, class comparison, or integer-degree cast is
redefined. Exactness uses the unchanged original restriction and forget maps.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- Every intrinsic current negative boundary equals the prescribed original boundary. -/
theorem currentNegativeConnecting_eq_original (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    currentNegativeConnecting f i a =
      boundedAboveFlatCoefficientNegativeLocalizationConnecting f i a := by
  have : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  have h := currentNegativeConnecting_correction f i a
  simpa only [GlobalSupportedParameterCoefficient.negativeClassCorrection_hom,
    GlobalParameterCoefficient.negativeClassCorrection_hom,
    Category.comp_id, Category.id_comp] using h

/-- The intrinsic boundary is exact after the original open restriction in every negative index. -/
theorem currentNegativeConnecting_exact_open (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Function.Exact ((boundedAboveFlatCoefficientOriginalNegativeKRestriction f i).app a)
      (currentNegativeConnecting f i a) := by
  rw [currentNegativeConnecting_eq_original]
  exact boundedAboveFlatCoefficientNegativeLocalizationConnecting_exact_open f i a

/-- The intrinsic boundary is exact before the original supported forget map in every index. -/
theorem currentNegativeConnecting_exact_supported (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Function.Exact (currentNegativeConnecting f i a)
      ((Bass.supportedNegativeKForgetNat (i + 1)).app
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a)) := by
  rw [currentNegativeConnecting_eq_original]
  exact boundedAboveFlatCoefficientNegativeLocalizationConnecting_exact_supported f i a

attribute [colib_tag "COL-1263"] currentNegativeConnecting_eq_original
attribute [colib_tag "COL-1263"] currentNegativeConnecting_exact_open
attribute [colib_tag "COL-1263"] currentNegativeConnecting_exact_supported

end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
