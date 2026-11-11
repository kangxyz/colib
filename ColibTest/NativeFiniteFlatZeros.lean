/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FiniteFlatZeros

/-! Scope examples for whole finite-flat zeros. These sources are UNCOMPILED. -/

open CategoryTheory AlgebraicGeometry Stacks.Divisors
open AlgebraicGeometry.Scheme.RelativeCurvePencil

universe u

example {C S : Scheme.{u}} (f : C ⟶ S) [SmoothOfRelativeDimension 1 f]
    (I : C.IdealSheafData) (hI : IsLocallyPrincipal I)
    [IsFinite (I.subschemeι ≫ f)] : Flat (I.subschemeι ≫ f) :=
  (relativeCartier_of_finite_locallyPrincipal f I hI).2

example {C S : Scheme.{u}} (f : C ⟶ S) [SmoothOfRelativeDimension 1 f]
    (I : C.IdealSheafData) (hI : IsLocallyPrincipal I)
    [IsFinite (I.subschemeι ≫ f)] : IsEffectiveCartierDivisor I :=
  (relativeCartier_of_finite_locallyPrincipal f I hI).1

example {C S : Scheme.{u}} (f : C ⟶ S) [SmoothOfRelativeDimension 1 f]
    [C.IsQuasiAffine] [IsAffine S] (I : C.IdealSheafData) (hI : IsLocallyPrincipal I)
    [IsProper (I.subschemeι ≫ f)] :
    IsFinite (I.subschemeι ≫ f) ∧ Flat (I.subschemeι ≫ f) := by
  obtain ⟨hfin, hrel⟩ := finite_relativeCartier_of_proper f I hI
  exact ⟨hfin, hrel.2⟩

example {C X S : Scheme.{u}} (p : X ⟶ S) [IsProper p] [IsAffine S]
    (j : C ⟶ X) [IsOpenImmersion j] [C.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ p)] (I : X.IdealSheafData)
    (hI : IsLocallyPrincipal I) (h : Set.range I.subschemeι ⊆ Set.range j) :
    IsFinite ((I.comap j).subschemeι ≫ (j ≫ p)) ∧
      Flat ((I.comap j).subschemeι ≫ (j ≫ p)) := by
  obtain ⟨hfin, hrel⟩ := finite_relativeCartier_on_open_of_proper p j I hI h
  exact ⟨hfin, hrel.2⟩

#check comapFiberιSubschemeIso_hom_base
#check relativeCartier_zeroScheme_of_finite
#check isIso_pullback_snd_of_whole_support
#check finite_relativeCartier_zeroScheme_on_open_of_proper
