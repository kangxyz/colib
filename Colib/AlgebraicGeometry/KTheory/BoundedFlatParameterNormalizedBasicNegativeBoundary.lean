/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterNormalizedBasicCurrentBoundary
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterNormalizedRowNegativeForget
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterCurrentNegativeBoundarySign

/-!
# The intrinsic basic normalized boundary on all original negative groups

The independently defined original finite classes and the original signed-degree
isomorphism identify the actual basic row boundary with the prescribed negative
localization boundary. The connecting map itself was defined from its own
path-space lift, before this comparison.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterNormalizedBasicLocalization
attribute [local instance] basicOver_compactSpace basicOver_quasiSeparatedSpace
open GlobalSectionChangeIndex GlobalSupportedSection SchemeNaturalSeed
attribute [local instance] GlobalSupportedParameterCoefficient.normalizedRowNegativeClass_isIso

private theorem original_classes_boundary {C : Type*} [Category C]
    {A B O S O' S' : C} (cO : A ⟶ O) (cS : B ⟶ S) [IsIso cS]
    (nO : A ⟶ O') (nS : B ⟶ S') [IsIso nS]
    (eO : O ⟶ O') (eS : S ⟶ S') (δc : O ⟶ S) (δn : O' ⟶ S')
    (hO : cO ≫ eO = nO) (hS : cS ≫ eS = nS) (hδ : δc ≫ eS = eO ≫ δn) :
    nO ≫ δn ≫ inv nS = cO ≫ δc ≫ inv cS := by
  apply (cancel_mono nS).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← hS, IsIso.inv_hom_id_assoc, hδ, ← Category.assoc, hO]

private theorem degree_square {C : Type*} [Category C] {A B D E G : C}
    (c : A ⟶ B) (d : B ⟶ D) (e : D ⟶ G) (v : B ⟶ E) (w : E ⟶ G) (n : A ⟶ E)
    (hd : v ≫ w = d ≫ e) (hc : c ≫ v = n) : (c ≫ d) ≫ e = n ≫ w := by
  rw [Category.assoc, ← hd, ← Category.assoc, hc]

private theorem ambient_degree_class
    (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    [CompactSpace P.left] [QuasiSeparatedSpace P.left]
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    ((GlobalParameterCoefficient.currentNegativeKComparison P i).hom.app a ≫
        (negativeLocalizationDegreeIso i).hom.app
          ((currentTelescope (ParameterLaurentTrack.ambientTrack P.left)).obj
            (specUnder.obj a))) ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ) + 1)).map
        (ParameterTensorNormalizedRowPresentation.ambientComparison P.left (specUnder.obj a)) =
    GlobalParameterCoefficient.normalizedRowNegativeClass P i a ≫
      (negativeLocalizationDegreeIso i).hom.app
        (ParameterTensorNormalizedRowPresentation.ambient P.left (specUnder.obj a)) :=
  degree_square _ _ _ _ _ _
    ((negativeLocalizationDegreeIso i).hom.naturality
      (ParameterTensorNormalizedRowPresentation.ambientComparison P.left (specUnder.obj a)))
    (GlobalParameterCoefficient.currentNegativeKComparison_normalizedRow P i a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem negative_boundary_of_current
    {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
    [QuasiSeparatedSpace Q.left] (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (δn : stableHomotopyGroup
        (ParameterTensorNormalizedRowPresentation.ambient P.left (specUnder.obj a))
        (-((i + 1 : ℕ) : ℤ) + 1) ⟶
      stableHomotopyGroup
        (ParameterTensorNormalizedRowPresentation.supported f.left (specUnder.obj a))
        (-((i + 1 : ℕ) : ℤ)))
    (hδ : ParameterFullCurrentNull.currentConnecting f a (-((i + 1 : ℕ) : ℤ)) ≫
        (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
          (ParameterTensorNormalizedRowPresentation.supportedComparison f.left (specUnder.obj a)) =
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ) + 1)).map
          (ParameterTensorNormalizedRowPresentation.ambientComparison P.left (specUnder.obj a)) ≫
        δn) :
    GlobalParameterCoefficient.normalizedRowNegativeClass P i a ≫
      (negativeLocalizationDegreeIso i).hom.app
        (ParameterTensorNormalizedRowPresentation.ambient P.left (specUnder.obj a)) ≫
      δn ≫ inv (GlobalSupportedParameterCoefficient.normalizedRowNegativeClass f (i + 1) a) =
    boundedAboveFlatCoefficientNegativeLocalizationConnecting f i a := by
  have : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  have h := original_classes_boundary _ _ _ _ _ _ _ _ (ambient_degree_class P i a)
    (GlobalSupportedParameterCoefficient.currentNegativeKComparison_normalizedRow f (i + 1) a) hδ
  calc
    _ = ParameterFullCurrentNull.currentNegativeConnecting f i a := by
      simpa only [ParameterFullCurrentNull.currentNegativeConnecting, NatIso.inv_hom_app,
        Iso.app_inv, Category.assoc] using h
    _ = _ := ParameterFullCurrentNull.currentNegativeConnecting_eq_original f i a

/-- The original supported negative class of the canonical basic inclusion is invertible. -/
theorem basicNormalizedNegativeClass_isIso (Q : Scheme.{u}) (U : Q.Opens)
    [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace U]
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsIso (GlobalSupportedParameterCoefficient.normalizedRowNegativeClass
      (basicOverInclusion Q U) i a) := by
  have : CompactSpace (Over.mk (specULiftZIsTerminal.from U.toScheme)).left :=
    basicOver_compactSpace U.toScheme
  have : CompactSpace (Over.mk (specULiftZIsTerminal.from Q)).left := basicOver_compactSpace Q
  have : QuasiSeparatedSpace (Over.mk (specULiftZIsTerminal.from Q)).left :=
    basicOver_quasiSeparatedSpace Q
  exact GlobalSupportedParameterCoefficient.normalizedRowNegativeClass_isIso
    (basicOverInclusion Q U) i a

attribute [local instance] basicNormalizedNegativeClass_isIso

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Every original basic negative boundary retains its independent class maps and degree cast. -/
theorem basicNegativeConnecting_eq_original (Q : Scheme.{u}) (U : Q.Opens)
    [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace U]
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    GlobalParameterCoefficient.normalizedRowNegativeClass
      (Over.mk (specULiftZIsTerminal.from U.toScheme)) i a ≫
      (negativeLocalizationDegreeIso i).hom.app
        (ParameterTensorNormalizedRowPresentation.ambient U.toScheme (specUnder.obj a)) ≫
      basicSpecConnecting Q U a (-((i + 1 : ℕ) : ℤ)) ≫
      inv (GlobalSupportedParameterCoefficient.normalizedRowNegativeClass
        (basicOverInclusion Q U) (i + 1) a) =
    boundedAboveFlatCoefficientNegativeLocalizationConnecting (basicOverInclusion Q U) i a := by
  exact negative_boundary_of_current (basicOverInclusion Q U) i a
    (basicSpecConnecting Q U a (-((i + 1 : ℕ) : ℤ)))
    (current_basic_normalized_connecting Q U a (-((i + 1 : ℕ) : ℤ)))

end AlgebraicGeometry.Scheme.Modules.ParameterNormalizedBasicLocalization
