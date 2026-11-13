/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryNormalizedRowLocalization

/-! # Same-null row localization with arbitrary signed degree and original support -/
noncomputable section
open Topology CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Topology.LoopPrespectrum AlgebraicGeometry.Scheme.Modules
open GlobalSupportedSection.ParameterAuxiliarySupport
open ParameterAuxiliaryNormalizedRowLocalization ParameterAuxiliaryCurrentFiber
universe u

example {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]
    (T : Q.Opens) [CompactSpace T] (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (normalizedPresentationLift f T (op (Spec (CommRingCat.of (ULift.{u} ℤ)))))) :=
  normalizedPresentationLift_integer_signed_isIso f T d

example {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (T : Q.Opens) (X : Scheme.{u}ᵒᵖ) :
    normalizedPresentationLift f T X ≫
      homotopyFiberProjection (normalizedPresentationRestriction f T X) =
      normalizedPresentationEnlargement f T X := normalizedPresentationLift_projection f T X

example {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (T : Q.Opens) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (t : unitInterval)
    (x : ((KTheory.Bass.SchemeNaturalSeed.currentTelescope
      (fiberAction f T)).obj X).space n) :
    (normalizedOpenPresentationComparison f T X).map n
        (((currentNull f T).homotopy X).level n (t, x)) =
      (normalizedPresentationNull f T X).level n
        (t, (normalizedFiberPresentationComparison f T X).map n x) :=
  normalizedPresentationNull_comparison f T X n t x
