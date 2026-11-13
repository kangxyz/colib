/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorPresentationLocalization
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorPresentationAuxiliary

/-! Original-null and negative-degree regressions for actual tensor ordinary presentations. -/
@[expose] public section
noncomputable section
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Topology.LoopPrespectrum KTheory.Bass AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
universe u
namespace ColibTest.ParameterTensorPresentationLocalization
open ParameterTensorPresentation ParameterAuxiliarySupport
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- Every actual negative stable degree sees the same auxiliary ordinary-presentation lift. -/
theorem original_auxiliary_negative (T : Q.Opens)
    [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace T] (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      (auxiliaryLift f T (op (Spec (CommRingCat.of (ULift.{u} ℤ)))))) :=
  auxiliaryLift_integer_isStableEquivalence f T (-(Int.ofNat k + 1))

/-- The original enlargement remains the actual projection of that same-null fiber lift. -/
theorem original_auxiliary_projection (T : Q.Opens) (X : Scheme.{u}ᵒᵖ) :
    auxiliaryLift f T X ≫ homotopyFiberProjection ((auxiliaryRestriction f T).app X) =
      (auxiliaryEnlargement f T).app X :=
  auxiliaryLift_projection f T X

end ColibTest.ParameterTensorPresentationLocalization
