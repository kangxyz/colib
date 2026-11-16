/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterSupportedCurrentNegativeClass
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterTelescopeComparison

/-!
# Original auxiliary-supported finite negative classes

The original supported negative groups are taken on the actual support arrows
for the union, auxiliary open, and inverse-image open. Their unchanged finite
negative comparisons are followed by the actual three auxiliary finite maps and
the original fine telescope inclusions. No current-to-fine comparison defines
these classes. Compactness of the inverse-image open uses the original compact
source and quasi-separated target hypotheses.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
ParameterAuxiliaryNegativeClasses.lean`, revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Topology.LoopPrespectrum KTheory.Bass
open KTheory.Bass.SchemeNaturalSeed
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection.ParameterAuxiliarySupport

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

omit [CompactSpace Q.left] [QuasiSeparatedSpace Q.left] in
/-- The original union support remains compact under the original localization hypotheses. -/
theorem unionOpen_compactSpace : CompactSpace (unionOpen f.left T) := by
  apply isCompact_iff_compactSpace.mp
  have hT : IsCompact (T : Set Q.left) :=
    isCompact_iff_compactSpace.mpr (show CompactSpace T from inferInstance)
  exact hT.union (isCompact_range f.left.continuous)

omit [IsOpenImmersion f.left] [CompactSpace Q.left] in
/-- Compactness of the inverse-image support uses compact source and quasi-separated target. -/
theorem inverseOpen_compactSpace : CompactSpace (inverseOpen f.left T) := by
  apply isCompact_iff_compactSpace.mp
  have hT : IsCompact (T : Set Q.left) :=
    isCompact_iff_compactSpace.mpr (show CompactSpace T from inferInstance)
  exact f.left.isCompact_preimage hT

include f in
omit [CompactSpace P.left] [CompactSpace Q.left] in
/-- The open scheme retains the original quasi-separated structure. -/
theorem open_quasiSeparatedSpace : QuasiSeparatedSpace P.left :=
  f.left.isOpenEmbedding.quasiSeparatedSpace

/-- The original supported finite-bottom class in the original fine auxiliary fiber telescope. -/
def fiberNegativeFineClass (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :=
  (GlobalSupportedParameterCoefficient.finiteNegativeKComparison
      (supportArrow Q (unionOpen f.left T)) i).hom.app a ≫
    (stableHomotopyFunctor (-(i : ℤ))).map ((fiberFiniteComparison f T i).app a) ≫
    (stableHomotopyFunctor (-(i : ℤ))).map
      ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeInclusion f T i).app a)

/-- The original supported finite-bottom class in the original fine auxiliary ambient telescope. -/
def ambientNegativeFineClass (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :=
  (GlobalSupportedParameterCoefficient.finiteNegativeKComparison (supportArrow Q T) i).hom.app a ≫
    (stableHomotopyFunctor (-(i : ℤ))).map ((ambientFiniteComparison Q T i).app a) ≫
    (stableHomotopyFunctor (-(i : ℤ))).map
      ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion T i).app a)

/-- The original supported finite-bottom class in the original fine full-open telescope. -/
def openNegativeFineClass (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :=
  (GlobalSupportedParameterCoefficient.finiteNegativeKComparison
      (supportArrow P (inverseOpen f.left T)) i).hom.app a ≫
    (stableHomotopyFunctor (-(i : ℤ))).map ((openFiniteComparison f T i).app a) ≫
    (stableHomotopyFunctor (-(i : ℤ))).map
      ((boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T i).app a)

end AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
