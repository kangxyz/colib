/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorPresentation
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialProofChoice

/-! Explicit proof-independent comparison formulas for the actual parameter Models. -/
/-!
Implementation provenance: adapted from Quillen at
`ParameterTensorComparisonChoice.lean` in its original source owner.
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole homotopies,
chosen nulls and proof terms are retained; namespaces and dependency owners are migrated.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology AlgebraicGeometry
open KTheory.Bass
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
open GlobalSectionChangeIndex SchemeTrackSequentialPresentation

/-- The fixed direction of the proved ambient whole-track equation. -/
theorem ambientTrack_transport_eq (Q : Scheme.{u}) :
    ParameterLaurentTrack.ambientTrack Q = ParameterTensorNormalizedTrack.ambientTrack Q :=
  (ParameterTensorNormalizedTrack.ambientTrack_eq Q).symm

/-- The fixed direction of the proved supported whole-track equation. -/
theorem supportedTrack_transport_eq {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] :
    ParameterLaurentTrack.supportedTrack f = ParameterTensorNormalizedTrack.supportedTrack f :=
  (ParameterTensorNormalizedTrack.supportedTrack_eq f).symm

/-- The actual ambient comparison uses the proved whole-track equation
independently of its proof. -/
theorem ambientComparison_eq_raw (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    ambientComparison Q X = comparisonOfEq (ParameterModels.ambient Q)
      (ParameterLaurentTrack.ambientTrack Q) (ParameterTensorNormalizedTrack.ambientTrack Q)
      (ambientTrack_transport_eq Q) X := by
  unfold ambientComparison
  apply comparisonOfEq_proof_irrel

/-- The supported comparison retains the same actual whole-track transport. -/
theorem supportedComparison_eq_raw {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ) :
    supportedComparison f X = comparisonOfEq (ParameterModels.supported f)
      (ParameterLaurentTrack.supportedTrack f) (ParameterTensorNormalizedTrack.supportedTrack f)
      (supportedTrack_transport_eq f) X := by
  unfold supportedComparison
  apply comparisonOfEq_proof_irrel

end AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
