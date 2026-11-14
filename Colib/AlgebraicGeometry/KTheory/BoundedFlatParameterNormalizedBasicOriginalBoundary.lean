/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterNormalizedBasicNegativeBoundary
public import Colib.AlgebraicGeometry.KTheory.Bass.SupportedLocalizationBoundary

/-!
# The intrinsic basic boundary on the absolute original negative groups

The identity coefficient retains the actual open and supported identity-base
projections. The original finite negative classes and their signed-degree cast
then compare the basic row's own boundary with the existing absolute original
localization boundary. No boundary or original class map is redefined.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterNormalizedBasicLocalization
open AlgebraicGeometry.Scheme.Bass AlgebraicGeometry.Scheme.Bass.SupportedLocalization
attribute [local instance] basicOver_compactSpace basicOver_quasiSeparatedSpace

/-- The displayed open inclusion as the original quasi-compact scheme/open pair. -/
abbrev basicOriginalPair (Q : Scheme.{u}) (U : Q.Opens) [CompactSpace Q] :
    Scheme.QuasiCompactOpenPairs.{u} :=
  ⟨MorphismProperty.Arrow.mk U.ι inferInstance, inferInstanceAs (CompactSpace Q)⟩

/-- The original displayed pair retains compactness of the removed open. -/
theorem basicOriginalPair_source_compact (Q : Scheme.{u}) (U : Q.Opens)
    [CompactSpace Q] [CompactSpace U] : CompactSpace (basicOriginalPair Q U).obj.left :=
  inferInstanceAs (CompactSpace U)

/-- The original displayed pair retains quasi-separatedness of the ambient scheme. -/
theorem basicOriginalPair_target_quasiSeparated (Q : Scheme.{u}) (U : Q.Opens)
    [CompactSpace Q] [QuasiSeparatedSpace Q] :
    QuasiSeparatedSpace (basicOriginalPair Q U).obj.right :=
  inferInstanceAs (QuasiSeparatedSpace Q)

attribute [local instance] basicOriginalPair_source_compact basicOriginalPair_target_quasiSeparated

/-- The original pair's integral-base arrow is the actual displayed basic inclusion. -/
theorem basicOriginalPair_localizationMap (Q : Scheme.{u}) (U : Q.Opens) [CompactSpace Q] :
    localizationMap (basicOriginalPair Q U) = basicOverInclusion Q U := rfl

/-- Identity coefficients recover the already defined intrinsic integer-parameter boundary. -/
theorem basicSpecConnecting_identity (Q : Scheme.{u}) (U : Q.Opens)
    [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace U] (d : ℤ) :
    basicSpecConnecting Q U identityCoefficient d = basicConnecting Q U d := rfl

private theorem identity_boundary_square {C : Type*} [Category C]
    {B E O S : C} (c : B ⟶ O) (b : E ⟶ S) [IsIso b] (δ : O ⟶ S) (k : B ⟶ E)
    (h : c ≫ δ ≫ inv b = k) {A D : C} (p : A ≅ B) (q : D ≅ E) :
    p.hom ≫ c ≫ δ = (p.hom ≫ k ≫ q.inv) ≫ q.hom ≫ b := by
  have h' := congrArg (fun f => p.hom ≫ f ≫ b) h
  simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc] using h'

/-- The actual identity projections preserve every absolute original negative boundary square. -/
theorem basicConnecting_original_negative_square (Q : Scheme.{u}) (U : Q.Opens)
    [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace U] (i : ℕ) :
    (identityOpenGroupIso (basicOriginalPair Q U) i).hom ≫
      GlobalParameterCoefficient.normalizedRowNegativeClass
        (Over.mk (specULiftZIsTerminal.from U.toScheme)) i identityCoefficient ≫
      (negativeLocalizationDegreeIso i).hom.app
        (ParameterTensorNormalizedRowPresentation.ambient U.toScheme
          (op (Spec (CommRingCat.of (ULift.{u} ℤ))))) ≫
      basicConnecting Q U (-((i + 1 : ℕ) : ℤ)) =
    supportedNegativeLocalizationConnecting (basicOriginalPair Q U) i ≫
      (identitySupportGroupIso (basicOriginalPair Q U) (i + 1)).hom ≫
      GlobalSupportedParameterCoefficient.normalizedRowNegativeClass
        (basicOverInclusion Q U) (i + 1) identityCoefficient := by
  have : IsIso (GlobalSupportedParameterCoefficient.normalizedRowNegativeClass
      (basicOverInclusion Q U) (i + 1) identityCoefficient) :=
    basicNormalizedNegativeClass_isIso Q U (i + 1) identityCoefficient
  have h := identity_boundary_square
    (GlobalParameterCoefficient.normalizedRowNegativeClass
      (Over.mk (specULiftZIsTerminal.from U.toScheme)) i identityCoefficient ≫
      (negativeLocalizationDegreeIso i).hom.app
        (ParameterTensorNormalizedRowPresentation.ambient U.toScheme
          (specUnder.obj identityCoefficient)))
    (GlobalSupportedParameterCoefficient.normalizedRowNegativeClass
      (basicOverInclusion Q U) (i + 1) identityCoefficient)
    (basicSpecConnecting Q U identityCoefficient (-((i + 1 : ℕ) : ℤ)))
    (boundedAboveFlatCoefficientNegativeLocalizationConnecting
      (basicOverInclusion Q U) i identityCoefficient)
    (by simpa only [Category.assoc] using
      basicNegativeConnecting_eq_original Q U i identityCoefficient)
    (identityOpenGroupIso (basicOriginalPair Q U) i)
    (identitySupportGroupIso (basicOriginalPair Q U) (i + 1))
  simp only [Category.assoc, basicSpecConnecting_identity,
    supportedNegativeLocalizationConnecting, basicOriginalPair_localizationMap] at h ⊢
  dsimp only [specUnder, identityCoefficient, basicOverInclusion, Under.mk, Over.homMk,
    ParameterTensorNormalizedRowPresentation.supported, stableHomotopyFunctor] at h ⊢
  exact h

end AlgebraicGeometry.Scheme.Modules.ParameterNormalizedBasicLocalization
