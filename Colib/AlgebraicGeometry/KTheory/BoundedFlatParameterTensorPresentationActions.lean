/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorPresentation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullCurrentNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryIteratedNullComparison

/-! Original basic and auxiliary arrows and null slices preserve
the genuine normalized tensor tracks. -/
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

/-- The original full-open map preserves the actual normalized tensor track. -/
theorem fullMap_equivariant : Equivariant (ambientTrack Q) (ambientTrack P)
    (ParameterFullCurrentNull.fullMap f) := by
  rw [ambientTrack_eq, ambientTrack_eq]
  exact ParameterFullCurrentNull.fullMap_equivariant f

/-- Every original basic null slice keeps its time and its normalized tensor action. -/
theorem fullNull_equivariant (r : unitInterval) :
    Equivariant (supportedTrack f) (ambientTrack P)
      (diagramHomotopyAt
        (η := Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor ≫
          ParameterFullCurrentNull.fullMap f)
        (θ := diagramZeroMap (ParameterModels.supported f ⋙ prespectrumFunctor)
          (ParameterModels.ambient P ⋙ prespectrumFunctor))
        (ParameterFullCurrentNull.fullNull f).homotopy
        (ParameterFullCurrentNull.fullNull f).naturality r) := by
  rw [supportedTrack_eq, ambientTrack_eq]
  exact ParameterFullCurrentNull.timeSlice_equivariant f r

open ParameterAuxiliarySupport
variable (T : Q.Opens)

/-- The actual union-support enlargement preserves the same normalized tensor action. -/
theorem enlargement_equivariant :
    Equivariant (supportedTrack (unionOpen f T).ι) (supportedTrack T.ι) (firstMap f T) := by
  rw [supportedTrack_eq, supportedTrack_eq]
  exact ParameterAuxiliarySupport.enlargement_equivariant f T

omit [IsOpenImmersion f] in
/-- The actual inverse-image support restriction preserves that normalized tensor action. -/
theorem restriction_equivariant :
    Equivariant (supportedTrack T.ι) (supportedTrack (inverseOpen f T).ι) (secondMap f T) := by
  rw [supportedTrack_eq, supportedTrack_eq]
  exact ParameterAuxiliarySupport.restriction_equivariant f T

/-- Every original auxiliary null slice retains its actual two-time tensor interchange. -/
theorem auxiliaryNull_equivariant (r : unitInterval) :
    Equivariant (supportedTrack (unionOpen f T).ι) (supportedTrack (inverseOpen f T).ι)
      (diagramHomotopyAt (η := firstMap f T ≫ secondMap f T)
        (θ := diagramZeroMap (fiber f T ⋙ prespectrumFunctor)
          (openModel f T ⋙ prespectrumFunctor))
        (fullNull f T).homotopy (fullNull f T).naturality r) := by
  rw [supportedTrack_eq, supportedTrack_eq]
  exact ParameterAuxiliarySupport.timeSlice_equivariant f T r

end AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
