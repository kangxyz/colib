/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedEvaluationSpectrum

/-! Full-signature consumers for the actual fixed-open supported evaluation. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory Topology
open scoped unitInterval
universe u
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineSupportedSectionEquivalence boundedAboveFlatAffineSupportedEvaluation
  boundedAboveFlatAffineSectionZero

example : LoopPrespectrum.Homotopy (boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap j
  ≫ boundedAboveFlatAffineSupportedSectionEvaluationInversePrespectrumMap j)
    (𝟙 (prespectrum (boundedAboveFlatAffineSupportedSectionModel j))) :=
      boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy j

example (n : ℕ) (x : (prespectrum (boundedAboveFlatAffineSupportedSectionModel j)).space n) :
    (boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy j).level n (0, x) =
      (boundedAboveFlatAffineSupportedSectionEvaluationInversePrespectrumMap j).map n
        ((boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap j).map n x) :=
        boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy_at_zero j n x

example (n : ℕ) (x : (prespectrum (boundedAboveFlatAffineSupportedSectionModel j)).space n) :
    (boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy j).level n (1, x) = x :=
      boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy_at_one j n x

example (n : ℕ) (s : unitInterval) :
    (boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy j).level n (s, (prespectrum
      (boundedAboveFlatAffineSupportedSectionModel j)).point n) =
      (prespectrum (boundedAboveFlatAffineSupportedSectionModel j)).point n :=
        boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy_at_point j n s

example (n : ℕ) (s t : unitInterval) (x : (prespectrum (boundedAboveFlatAffineSupportedSectionModel
  j)).space n) :
    (boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy j).level (n + 1) (s, (prespectrum
      (boundedAboveFlatAffineSupportedSectionModel j)).structureMap n x t) =
      (prespectrum (boundedAboveFlatAffineSupportedSectionModel j)).structureMap n
        ((boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy j).level n (s, x)) t :=
  boundedAboveFlatAffineSupportedSectionEvaluationLeftHomotopy_comm j n s t x

example : LoopPrespectrum.Homotopy
  (boundedAboveFlatAffineSupportedSectionEvaluationInversePrespectrumMap j ≫
  boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap j)
    (𝟙 (originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j))) :=
      boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy j

example (n : ℕ) (x : (originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j)).space n) :
    (boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy j).level n (0, x) =
      (boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap j).map n
        ((boundedAboveFlatAffineSupportedSectionEvaluationInversePrespectrumMap j).map n x) :=
        boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy_at_zero j n x

example (n : ℕ) (x : (originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j)).space n) :
    (boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy j).level n (1, x) = x :=
      boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy_at_one j n x

example (n : ℕ) (s : unitInterval) :
    (boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy j).level n (s,
      (originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j)).point n) =
      (originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j)).point n :=
        boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy_at_point j n s

example (n : ℕ) (s t : unitInterval) (x : (originalPrespectrum
  (boundedAboveFlatPerfectSupportedWaldhausen j)).space n) :
    (boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy j).level (n + 1) (s,
      (originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j)).structureMap n x t) =
      (originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j)).structureMap n
        ((boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy j).level n (s, x)) t :=
  boundedAboveFlatAffineSupportedSectionEvaluationRightHomotopy_comm j n s t x
