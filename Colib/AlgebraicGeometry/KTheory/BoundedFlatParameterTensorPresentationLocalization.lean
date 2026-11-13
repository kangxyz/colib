/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorPresentationActions
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorPresentationDiagram
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterCurrentFullFiber
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialNullTransport
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialLiftTransport
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorComparisonChoice

/-! The actual basic localization maps and original null
on normalized tensor ordinary presentations. -/
/-!
Implementation provenance: adapted from Quillen at
`ParameterTensorPresentationLocalization.lean` in its original source owner.
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole homotopies,
chosen nulls and proof terms are retained; namespaces and dependency owners are migrated.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
open GlobalSectionChangeIndex ParameterTensorNormalizedTrack
open SchemeTrackSequentialPresentation
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The original support forgetful map induces the actual ordinary-colimit map. -/
def basicForget : supportedDiagram f ⟶ ambientDiagram Q := ordinaryInputMap
  (ParameterModels.supported f) (ParameterModels.ambient Q)
  (supportedTrack f) (ambientTrack Q)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (forget_equivariant f)

/-- The original full-open restriction induces the actual ordinary-colimit map. -/
def basicRestriction : ambientDiagram Q ⟶ ambientDiagram P := ordinaryInputMap
  (ParameterModels.ambient Q) (ParameterModels.ambient P)
  (ambientTrack Q) (ambientTrack P) (ParameterFullCurrentNull.fullMap f) (fullMap_equivariant f)

/-- The actual ordinary presentation retains the original full-open null at every time. -/
def basicNull : DiagramNullHomotopy (basicForget f) (basicRestriction f) := ordinaryInputNull
  (ParameterModels.supported f) (ParameterModels.ambient Q)
  (supportedTrack f) (ambientTrack Q)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (forget_equivariant f)
  (ParameterModels.ambient P) (ambientTrack P) (ParameterFullCurrentNull.fullMap f)
  (fullMap_equivariant f) (ParameterFullCurrentNull.fullNull f) (fullNull_equivariant f)

/-- The specified original null supplies the actual ordinary-presentation fiber lift. -/
def basicLift (X : Scheme.{u}ᵒᵖ) :
    supported f X ⟶ homotopyFiber ((basicRestriction f).app X) :=
  homotopyFiberLift ((basicRestriction f).app X) ((basicForget f).app X)
    ((basicNull f).homotopy X)

/-- The actual comparison preserves the original full-open null at exactly the same time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterTensorPresentationLocalization.lean:56"
  "adaptation" "Original tensor presentation localization with the same selected null."]
theorem basicNull_comparison (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (q : ((SchemeNaturalSeed.currentTelescope
      (ParameterLaurentTrack.supportedTrack f)).obj X).space n) :
    type_of% (ordinaryInputNull_comparisonOfEq
    (ParameterModels.supported f) (ParameterModels.ambient Q) (ParameterModels.ambient P)
    (ParameterLaurentTrack.supportedTrack f) (supportedTrack f)
    (ParameterLaurentTrack.ambientTrack Q) (ambientTrack Q)
    (ParameterLaurentTrack.ambientTrack P) (ambientTrack P)
    (supportedTrack_transport_eq f) (ambientTrack_transport_eq Q) (ambientTrack_transport_eq P)
    (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor)
    (ParameterFullCurrentNull.fullMap f)
    (ParameterLaurentTrack.forget_equivariant f) (ParameterFullCurrentNull.fullMap_equivariant f)
    (forget_equivariant f) (fullMap_equivariant f) (ParameterFullCurrentNull.fullNull f)
    (ParameterFullCurrentNull.timeSlice_equivariant f) (fullNull_equivariant f) X n r q) :=
  ordinaryInputNull_comparisonOfEq
    (ParameterModels.supported f) (ParameterModels.ambient Q) (ParameterModels.ambient P)
    (ParameterLaurentTrack.supportedTrack f) (supportedTrack f)
    (ParameterLaurentTrack.ambientTrack Q) (ambientTrack Q)
    (ParameterLaurentTrack.ambientTrack P) (ambientTrack P)
    (supportedTrack_transport_eq f) (ambientTrack_transport_eq Q) (ambientTrack_transport_eq P)
    (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor)
    (ParameterFullCurrentNull.fullMap f)
    (ParameterLaurentTrack.forget_equivariant f) (ParameterFullCurrentNull.fullMap_equivariant f)
    (forget_equivariant f) (fullMap_equivariant f) (ParameterFullCurrentNull.fullNull f)
    (ParameterFullCurrentNull.timeSlice_equivariant f) (fullNull_equivariant f) X n r q
/-- The original basic localization theorem transports to this same-null ordinary lift. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterTensorPresentationLocalization.lean:82"
  "adaptation" "Original tensor presentation localization with the same selected null."]
theorem basicLift_integer_isStableEquivalence
    [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q] :
    IsStableEquivalence (basicLift f (op (Spec (CommRingCat.of (ULift.{u} ℤ))))) := by
  have hs := ParameterFullCurrentNull.currentLift_integer_isStableEquivalence f
  dsimp only [ParameterFullCurrentNull.currentLift, ParameterFullCurrentNull.currentOpen,
    ParameterFullCurrentNull.currentForget, ParameterFullCurrentNull.currentNull] at hs
  have h := ordinaryInputLift_stableOfEq
    (ParameterModels.supported f) (ParameterModels.ambient Q) (ParameterModels.ambient P)
    (ParameterLaurentTrack.supportedTrack f) (supportedTrack f)
    (ParameterLaurentTrack.ambientTrack Q) (ambientTrack Q)
    (ParameterLaurentTrack.ambientTrack P) (ambientTrack P)
    (supportedTrack_transport_eq f) (ambientTrack_transport_eq Q) (ambientTrack_transport_eq P)
    (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor)
    (ParameterFullCurrentNull.fullMap f)
    (ParameterLaurentTrack.forget_equivariant f) (ParameterFullCurrentNull.fullMap_equivariant f)
    (forget_equivariant f) (fullMap_equivariant f) (ParameterFullCurrentNull.fullNull f)
    (ParameterFullCurrentNull.timeSlice_equivariant f) (fullNull_equivariant f)
    (op (Spec (CommRingCat.of (ULift.{u} ℤ)))) hs
  dsimp only [basicLift, basicNull, basicForget, basicRestriction,
    ambient, supported, ambientDiagram, supportedDiagram]
  exact h

/-- The fiber projection is exactly the actual ordinary support-forgetting map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterTensorPresentationLocalization.lean:104"
  "adaptation" "Original tensor presentation localization with the same selected null."]
theorem basicLift_projection (X : Scheme.{u}ᵒᵖ) :
    basicLift f X ≫ homotopyFiberProjection ((basicRestriction f).app X) =
      (basicForget f).app X :=
  homotopyFiberLift_projection _ _ _

end AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation

namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation

attribute [colib_tag "COL-0599"] basicLift_integer_isStableEquivalence

end AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
