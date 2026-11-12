/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryCurrentLocalization
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryNormalizedRowPresentationNull

/-!
# Same-null localization for the normalized independent-boundary presentation

The original auxiliary lift transfers through the three genuine normalized
presentation comparisons. The maps retain their original source null and the
full independent normalization homotopy. Complete tensor-return provenance and
original class-map identification remain separate classical-qualification obligations.
-/
@[expose] public section
noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryNormalizedRowLocalization
open GlobalSupportedSection GlobalSectionChangeIndex ParameterAuxiliarySupport
  ParameterAuxiliaryCurrentFiber
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The original auxiliary null defines the actual path-space lift on the row presentations. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowL\
    ocalization.lean:34"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def normalizedPresentationLift (X : Scheme.{u}ᵒᵖ) :=
  homotopyFiberLift (normalizedPresentationRestriction f T X)
    (normalizedPresentationEnlargement f T X)
    (normalizedPresentationNull f T X)

/-- The specified full null gives the strict square of the original path-space lifts. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowL\
    ocalization.lean:40"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem current_normalized_lift_square (X : Scheme.{u}ᵒᵖ) :
    currentLift f T X ≫ homotopyFiberMap
        (Arrow.homMk (f := Arrow.mk ((currentRestriction f T).app X))
          (g := Arrow.mk (normalizedPresentationRestriction f T X))
          (normalizedAmbientPresentationComparison T X) (normalizedOpenPresentationComparison f T X)
          (normalizedPresentationRestriction_square f T X).symm) =
      normalizedFiberPresentationComparison f T X ≫ normalizedPresentationLift f T X :=
  homotopyFiberLift_naturality
    ((currentEnlargement f T).app X) ((currentRestriction f T).app X)
    (normalizedPresentationEnlargement f T X) (normalizedPresentationRestriction f T X)
    ((currentNull f T).homotopy X) (normalizedPresentationNull f T X)
    (normalizedFiberPresentationComparison f T X) (normalizedAmbientPresentationComparison T X)
    (normalizedOpenPresentationComparison f T X)
    (normalizedPresentationEnlargement_square f T X)
    (normalizedPresentationRestriction_square f T X).symm
    (normalizedPresentationNull_comparison f T X)

/-- All three genuine comparisons transport the entire same-null fiber lift. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowL\
    ocalization.lean:58"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem current_normalized_lift_stable_iff (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (currentLift f T X) ↔
      IsStableEquivalence (normalizedPresentationLift f T X) :=
  homotopyFiberLift_isStableEquivalence_iff
    ((currentEnlargement f T).app X) ((currentRestriction f T).app X)
    (normalizedPresentationEnlargement f T X) (normalizedPresentationRestriction f T X)
    ((currentNull f T).homotopy X) (normalizedPresentationNull f T X)
    (normalizedFiberPresentationComparison f T X) (normalizedAmbientPresentationComparison T X)
    (normalizedOpenPresentationComparison f T X)
    (normalizedPresentationEnlargement_square f T X)
    (normalizedPresentationRestriction_square f T X).symm
    (normalizedPresentationNull_comparison f T X)
    (ParameterTensorNormalizedRowPresentation.supportedComparison_stable (unionOpen f T).ι X)
    (ParameterTensorNormalizedRowPresentation.supportedComparison_stable T.ι X)
    (ParameterTensorNormalizedRowPresentation.supportedComparison_stable (inverseOpen f T).ι X)

/-- The actual integer-base auxiliary row lift is stable with the original G7 hypotheses. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowL\
    ocalization.lean:75"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedPresentationLift_integer_isStableEquivalence
    [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace T] :
    IsStableEquivalence (normalizedPresentationLift f T (op (Spec (CommRingCat.of (ULift.{u}
      ℤ))))) :=
  (current_normalized_lift_stable_iff f T (op (Spec (CommRingCat.of (ULift.{u} ℤ))))).mp
    (currentLift_integer_isStableEquivalence f T)

/-- The same prescribed lift is stable at every original affine base parameter. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowL\
    ocalization.lean:82"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedPresentationLift_spec_isStableEquivalence
    {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
    [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (normalizedPresentationLift f.left T (specUnder.obj a)) :=
  (current_normalized_lift_stable_iff f.left T (specUnder.obj a)).mp
    (currentLift_spec_isStableEquivalence f T a)

/-- Every original signed stable degree sees the same actual presentation lift. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowL\
    ocalization.lean:92"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedPresentationLift_integer_signed_isIso
    [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace T] (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (normalizedPresentationLift f T (op (Spec
      (CommRingCat.of (ULift.{u} ℤ)))))) :=
  normalizedPresentationLift_integer_isStableEquivalence f T d

/-- Projection of the same lift is precisely the original presentation enlargement. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowL\
    ocalization.lean:98"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedPresentationLift_projection (X : Scheme.{u}ᵒᵖ) :
    normalizedPresentationLift f T X ≫
      homotopyFiberProjection (normalizedPresentationRestriction f T X) =
      normalizedPresentationEnlargement f T X :=
  homotopyFiberLift_projection _ _ _

end AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryNormalizedRowLocalization
