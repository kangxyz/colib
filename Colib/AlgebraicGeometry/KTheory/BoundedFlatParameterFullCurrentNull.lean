/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeInputNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterLaurentNull

/-! # The original supported parameter null on current and normalized towers -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
open SchemeNaturalSeed NaturalTrack
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The original full-open arrow is the literal weak-change followed by restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullCurrentNull.lean:26"
  "adaptation" "Original actual full-open map and same selected whole null."]
def fullMap := Functor.whiskerRight (ParameterModels.changeWeak f) prespectrumFunctor ≫
  Functor.whiskerRight (ParameterModels.openRestriction f) prespectrumFunctor

/-- The original selected null postcomposed by actual full-open restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullCurrentNull.lean:30"
  "adaptation" "Original actual full-open map and same selected whole null."]
def fullNull : DiagramNullHomotopy
    (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (fullMap f) where
  homotopy X := (((ParameterModels.supportedOpenNull f).homotopy X).postcomp
    (prespectrumMap ((ParameterModels.openRestriction f).app X))).cast
      (Category.assoc _ _ _)
      (by
        apply Topology.LoopPrespectrum.Hom.ext
        funext n
        ext x
        exact (prespectrumMap ((ParameterModels.openRestriction f).app X)).map_point n)
  naturality {X Y} g n r x := by
    exact (congrArg (fun k => k.map n
      (((ParameterModels.supportedOpenNull f).homotopy X).level n (r, x)))
      ((Functor.whiskerRight (ParameterModels.openRestriction f)
        prespectrumFunctor).naturality g)).symm.trans
      (congrArg (fun y => (prespectrumMap
        ((ParameterModels.openRestriction f).app Y)).map n y)
        ((ParameterModels.supportedOpenNull f).naturality g n r x))

/-- Every original full-open null slice commutes with the original scalar action. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullCurrentNull.lean:50"
  "adaptation" "Original actual full-open map and same selected whole null."]
theorem timeSlice_equivariant (r : unitInterval) :
    Equivariant (supportedTrack f) (ambientTrack P)
      (diagramHomotopyAt
        (η := Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor ≫ fullMap f)
        (θ := diagramZeroMap (ParameterModels.supported f ⋙ prespectrumFunctor)
          (ParameterModels.ambient P ⋙ prespectrumFunctor))
        (fullNull f).homotopy (fullNull f).naturality r) := by
  intro X t
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  ext x
  exact (ParameterLaurentNull.fullOpenNull_laurentInterchange f X n r t x).symm

/-- The original two actual maps preserve the full-open scalar action. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullCurrentNull.lean:64"
  "adaptation" "Original actual full-open map and same selected whole null."]
theorem fullMap_equivariant : Equivariant (ambientTrack Q) (ambientTrack P) (fullMap f) :=
  (changeWeak_equivariant f).comp (openRestriction_equivariant f)

/-- The original full-open null on the current telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullCurrentNull.lean:68"
  "adaptation" "Original actual full-open map and same selected whole null."]
def currentNull := currentInputNull (supportedTrack f) (ambientTrack Q) (ambientTrack P)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (fullMap f)
  (forget_equivariant f) (fullMap_equivariant f) (fullNull f) (timeSlice_equivariant f)

/-- The original full-open null on the normalized telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullCurrentNull.lean:73"
  "adaptation" "Original actual full-open map and same selected whole null."]
def normalizedNull := normalizedInputNull (supportedTrack f) (ambientTrack Q) (ambientTrack P)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (fullMap f)
  (forget_equivariant f) (fullMap_equivariant f) (fullNull f) (timeSlice_equivariant f)

/-- The actual full-open original null is preserved at all points and all times. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullCurrentNull.lean:83"
  "adaptation" "Original actual full-open map and same selected whole null."]
theorem current_null_square (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((currentTelescope (supportedTrack f)).obj X).space n) :
    ((telescopeMap (ambientTrack P)).app X).map n
      (((currentNull f).homotopy X).level n (r, x)) =
      ((normalizedNull f).homotopy X).level n
        (r, ((telescopeMap (supportedTrack f)).app X).map n x) :=
  telescopeMap_null _ _ _ _ _ (forget_equivariant f) (fullMap_equivariant f)
    (fullNull f) (timeSlice_equivariant f) X n r x


end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull

namespace AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull

attribute [colib_tag "COL-0568"] current_null_square

end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
