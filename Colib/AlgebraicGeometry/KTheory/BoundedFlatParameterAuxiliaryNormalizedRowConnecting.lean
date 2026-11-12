/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryNormalizedRowLocalization
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryIntrinsicConnecting

/-!
Source:
Quillen source module
`AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowConnecting.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The intrinsic boundary of the actual normalized auxiliary row

The connecting map is formed from the normalized row's own restriction,
enlargement, whole null, and proved path-space fiber lift. The original
current boundary is then compared by the actual same-null naturality theorem.
The definition is independent of a transported current or fine boundary.
-/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryNormalizedRowLocalization
open GlobalSupportedSection GlobalSectionChangeIndex ParameterAuxiliarySupport
  ParameterAuxiliaryCurrentFiber
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

/-- The actual normalized row's own signed path-space boundary in every integer degree. -/
def normalizedPresentationConnecting (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup
      (ParameterTensorNormalizedRowPresentation.supported (inverseOpen f.left T).ι
        (specUnder.obj a)) (d + 1) ⟶
      stableHomotopyGroup
        (ParameterTensorNormalizedRowPresentation.supported (unionOpen f.left T).ι
          (specUnder.obj a)) d := by
  have : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift
        (normalizedPresentationRestriction f.left T (specUnder.obj a))
        (normalizedPresentationEnlargement f.left T (specUnder.obj a))
        (normalizedPresentationNull f.left T (specUnder.obj a)))) :=
    normalizedPresentationLift_spec_isStableEquivalence f T a d
  exact stableFiberLiftConnecting
    (normalizedPresentationEnlargement f.left T (specUnder.obj a))
    (normalizedPresentationRestriction f.left T (specUnder.obj a))
    (normalizedPresentationNull f.left T (specUnder.obj a)) d

/-- The original current boundary follows the genuine normalized comparison and whole null. -/
@[reassoc]
theorem current_normalizedPresentation_connecting
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    currentConnecting f T a d ≫ (stableHomotopyFunctor d).map
        (normalizedFiberPresentationComparison f.left T (specUnder.obj a)) =
      (stableHomotopyFunctor (d + 1)).map
          (normalizedOpenPresentationComparison f.left T (specUnder.obj a)) ≫
        normalizedPresentationConnecting f T a d := by
  have : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((currentRestriction f.left T).app (specUnder.obj a))
        ((currentEnlargement f.left T).app (specUnder.obj a))
        ((currentNull f.left T).homotopy (specUnder.obj a)))) :=
    currentLift_spec_isStableEquivalence f T a d
  have : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift
        (normalizedPresentationRestriction f.left T (specUnder.obj a))
        (normalizedPresentationEnlargement f.left T (specUnder.obj a))
        (normalizedPresentationNull f.left T (specUnder.obj a)))) :=
    normalizedPresentationLift_spec_isStableEquivalence f T a d
  exact stableFiberLiftConnecting_naturality
    ((currentEnlargement f.left T).app (specUnder.obj a))
    ((currentRestriction f.left T).app (specUnder.obj a))
    (normalizedPresentationEnlargement f.left T (specUnder.obj a))
    (normalizedPresentationRestriction f.left T (specUnder.obj a))
    ((currentNull f.left T).homotopy (specUnder.obj a))
    (normalizedPresentationNull f.left T (specUnder.obj a))
    (normalizedFiberPresentationComparison f.left T (specUnder.obj a))
    (normalizedAmbientPresentationComparison T (specUnder.obj a))
    (normalizedOpenPresentationComparison f.left T (specUnder.obj a))
    (normalizedPresentationEnlargement_square f.left T (specUnder.obj a))
    (normalizedPresentationRestriction_square f.left T (specUnder.obj a)).symm
    (normalizedPresentationNull_comparison f.left T (specUnder.obj a)) d

end AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryNormalizedRowLocalization
