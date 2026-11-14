/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorPresentation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullPresentationActions
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryPresentationActions

/-! Equivariance for support-forgetting, with re-exports for the full and auxiliary open actions. -/
/-!
Implementation provenance: adapted from Quillen at
`ParameterTensorPresentationActions.lean` in its original source owner.
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole homotopies,
chosen nulls and proof terms are retained; namespaces and dependency owners are migrated.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
open GlobalSectionChangeIndex NaturalTrack ParameterTensorNormalizedTrack
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The original support forgetful map preserves the actual normalized tensor track. -/
theorem forget_equivariant : Equivariant (supportedTrack f) (ambientTrack Q)
    (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) := by
  rw [supportedTrack_eq, ambientTrack_eq]
  exact ParameterLaurentTrack.forget_equivariant f

end AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
