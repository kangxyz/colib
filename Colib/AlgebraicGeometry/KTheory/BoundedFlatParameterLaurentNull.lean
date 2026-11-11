/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterOpenTrack
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalOpenPairNull
public import Colib.KTheory.Waldhausen.Iterated.DiagramNullIdentityAction

/-!
# The original parameter localization null preserves the original Laurent track

Both interval parameters stay independent. The null is the original reversed
weak zero-to-inclusion realization, and the scalar is the original parameter
Laurent coordinate on the actual supported and relative-open Models.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterLaurentNull
open GlobalSupportedSection ParameterLaurentTrack
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The literal support-forget/change-weak composite preserves the same original unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterLaurentNull.lean:34"
  "adaptation" "Original whole supported null and independent Laurent action time."]
theorem supportedOpen_unit (X : Scheme.{u}ᵒᵖ) :
    Preserves (((ParameterModels.forget f).app (laurent.op.obj X) ≫
      (ParameterModels.changeWeak f).app (laurent.op.obj X)).hom.toFunctor)
      (supportedUnit f X) (openUnit f X) := by
  intro S
  exact (congrArg (((ParameterModels.changeWeak f).app (laurent.op.obj X)).hom.toFunctor.map)
    (forget_unit f X S)).trans
      (changeWeak_unit f X
        (((ParameterModels.forget f).app (laurent.op.obj X)).hom.toFunctor.obj S))

/-- The original reversed zero-to-image null commutes with compatible identity actions. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterLaurentNull.lean:44"
  "adaptation" "Original whole supported null and independent Laurent action time."]
theorem supportedOpenNull_unitCompatible (X : Scheme.{u}ᵒᵖ) :
    ZeroNullUnitCompatible ((ParameterModels.forget f).app X)
      ((ParameterModels.changeWeak f).app X)
      ((ParameterModels.supportedOpenNull f).homotopy X) :=
  prespectrumCompositeZeroNullHomotopy_unitCompatible
    ((ParameterModels.forget f).app X) ((ParameterModels.changeWeak f).app X)
    (ParameterModels.zeroToOpen f X) (ParameterModels.zeroToOpen_weak f X)

/-- The original null time and the actual Laurent scalar-track time remain independent. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterLaurentNull.lean:53"
  "adaptation" "Original whole supported null and independent Laurent action time."]
theorem supportedOpenNull_laurentInterchange (X : Scheme.{u}ᵒᵖ) :
    TrackInterchange ((ParameterModels.supportedOpenNull f).homotopy X)
      ((ParameterModels.supportedOpenNull f).homotopy (laurent.op.obj X))
      ((supportedTrack f).homotopy X) ((openTrack f).homotopy X) :=
  modelDiagramNull_coefficientCompatible
    (r := ParameterModels.forget f) (q := ParameterModels.changeWeak f)
    (ParameterModels.supportedOpenNull f) (coefficient.app X)
    (supportedUnit f X) (openUnit f X)
    (supportedOpenNull_unitCompatible f (laurent.op.obj X) _ _ (supportedOpen_unit f X))

/-- Postcomposition by the original open restriction keeps both null and scalar times. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterLaurentNull.lean:64"
  "adaptation" "Original whole supported null and independent Laurent action time."]
theorem fullOpenNull_laurentInterchange (X : Scheme.{u}ᵒᵖ) :
    TrackInterchange
      (((ParameterModels.supportedOpenNull f).homotopy X).postcomp
        (prespectrumMap ((ParameterModels.openRestriction f).app X)))
      (((ParameterModels.supportedOpenNull f).homotopy (laurent.op.obj X)).postcomp
        (prespectrumMap ((ParameterModels.openRestriction f).app (laurent.op.obj X))))
      ((supportedTrack f).homotopy X) ((ambientTrack P).homotopy X) := by
  intro n s t x
  change (prespectrumMap ((ParameterModels.openRestriction f).app (laurent.op.obj X))).map n
      (((ParameterModels.supportedOpenNull f).homotopy (laurent.op.obj X)).level n
        (s, ((supportedTrack f).homotopy X).level n (t, x))) = _
  exact (congrArg
    (fun y => (prespectrumMap
      ((ParameterModels.openRestriction f).app (laurent.op.obj X))).map n y)
    (supportedOpenNull_laurentInterchange f X n s t x)).trans
      (congrArg (fun k => k.map n
        (((ParameterModels.supportedOpenNull f).homotopy X).level n (s, x)))
          (openRestriction_equivariant f X t)).symm

end AlgebraicGeometry.Scheme.Modules.ParameterLaurentNull
