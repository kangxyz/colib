/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeConjugationAllSign
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeAffineDoubleContractionSign
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterCorrectionFiniteIdentity
public import Colib.AlgebraicGeometry.KTheory.Bass.NativeAmbientModelZeroComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedParameterStableZeroSwap

/-!
# All original negative-class corrections from the actual coefficient swap sign

The actual integral-coefficient spectra determine the swap on affine parameters
through the canonical Spec–Gamma isomorphism. This genuine Laurent-closed family
feeds the original finite-word calculation. The original finite negative-class
isomorphisms are unchanged, both for ambient and for supported coefficients.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme PolynomialLaurent.Relative
open KTheory.Bass.SchemeNaturalSeed KTheory.Bass.GeometricConeInterchange
universe u
namespace AlgebraicGeometry.Scheme.Modules
open GlobalSectionChangeIndex GlobalSupportedSection
open KTheory.Bass.TwoChart

namespace GlobalParameterCoefficient
variable (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
  [CompactSpace P.left] [QuasiSeparatedSpace P.left]

omit [QuasiSeparatedSpace P.left] in
/-- The actual affine coefficient swap sign makes every original ambient correction identity. -/
theorem negativeClassCorrection_hom_of_spec_swap
    (h : ∀ b, doubleContractionSwap (quasiCompactStableZero (parameterDiagram P))
      (coefficientParameterScheme b) = -𝟙 _)
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (negativeClassCorrection P i a).hom = 𝟙 _ := by
  apply negativeClassCorrection_hom_of_finite_id P i a
  have : IsAffine (coefficientParameterScheme a).unop.obj :=
    inferInstanceAs (IsAffine (Spec a.right))
  exact finiteStageStableIso_neg_nat_id (fun X => IsAffine X.unop.obj)
    (ParameterModels.ambient P.left)
    (by
      intro X hX
      have : IsAffine X.unop.obj := hX
      exact doubleContractionSwap_neg_affine_of_under_spec
        (quasiCompactStableZero (parameterDiagram P)) h X)
    isAffine_laurent_parameter i (coefficientParameterScheme a) inferInstance

/-- The genuine parameter quotient sign makes every original finite correction trivial. -/
theorem negativeClassCorrection_hom (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (negativeClassCorrection P i a).hom = 𝟙 _ := by
  apply negativeClassCorrection_hom_of_spec_swap P _ i a
  intro b
  let : QuasiSeparatedSpace (coefficientParameterScheme b).unop.obj :=
    inferInstanceAs (QuasiSeparatedSpace (Spec b.right))
  exact parameter_doubleContractionSwap_neg P (coefficientParameterScheme b)

/-- The specified current-to-fine comparison preserves the original negative class map. -/
@[reassoc]
theorem currentNegativeKComparison_fine (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (currentNegativeKComparison P i).hom.app a ≫
        (currentIteratedStableIso (ParameterModels.ambient P.left)
          (ParameterLaurentTrack.ambientTrack P.left) (specUnder.obj a) (-(i : ℤ))).hom ≫
        (stableHomotopyFunctor (-(i : ℤ))).map ((fineTelescopeComparison P).app a) =
      (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom.app a := by
  rw [currentNegativeKComparison_fine_correction, negativeClassCorrection_hom, Category.id_comp]

end GlobalParameterCoefficient

namespace GlobalSupportedParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

omit [CompactSpace P.left] [QuasiSeparatedSpace Q.left] in
/-- The actual supported coefficient swap sign fixes every unchanged supported negative class. -/
theorem negativeClassCorrection_hom_of_spec_swap
    (h : ∀ b, doubleContractionSwap (quasiCompactStableZero (parameterDiagram f))
      (coefficientParameterScheme b) = -𝟙 _)
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (negativeClassCorrection f i a).hom = 𝟙 _ := by
  apply negativeClassCorrection_hom_of_finite_id f i a
  have : IsAffine (coefficientParameterScheme a).unop.obj :=
    inferInstanceAs (IsAffine (Spec a.right))
  exact finiteStageStableIso_neg_nat_id (fun X => IsAffine X.unop.obj)
    (ParameterModels.supported f.left)
    (by
      intro X hX
      have : IsAffine X.unop.obj := hX
      exact doubleContractionSwap_neg_affine_of_under_spec
        (quasiCompactStableZero (parameterDiagram f)) h X)
    isAffine_laurent_parameter i (coefficientParameterScheme a) inferInstance

/-- The genuine parameter quotient sign makes every original finite correction trivial. -/
theorem negativeClassCorrection_hom (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (negativeClassCorrection f i a).hom = 𝟙 _ := by
  apply negativeClassCorrection_hom_of_spec_swap f _ i a
  intro b
  exact SupportedParameterCoefficientUnitOperation.parameterDiagram_quotient_swap f b

/-- The specified current-to-fine comparison preserves the original negative class map. -/
@[reassoc]
theorem currentNegativeKComparison_fine (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (currentNegativeKComparison f i).hom.app a ≫
        (currentIteratedStableIso (ParameterModels.supported f.left)
          (ParameterLaurentTrack.supportedTrack f.left) (specUnder.obj a) (-(i : ℤ))).hom ≫
        (stableHomotopyFunctor (-(i : ℤ))).map ((fineTelescopeComparison f).app a) =
      (boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison f i).hom.app a := by
  rw [currentNegativeKComparison_fine_correction, negativeClassCorrection_hom, Category.id_comp]

end GlobalSupportedParameterCoefficient
end AlgebraicGeometry.Scheme.Modules
