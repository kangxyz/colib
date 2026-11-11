module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterLaurentNull

open CategoryTheory Topology Opposite AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
universe u
noncomputable section
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
example (X : Scheme.{u}ᵒᵖ) :
    ZeroNullUnitCompatible ((ParameterModels.forget f).app X)
      ((ParameterModels.changeWeak f).app X)
      ((ParameterModels.supportedOpenNull f).homotopy X) :=
  ParameterLaurentNull.supportedOpenNull_unitCompatible f X
example (X : Scheme.{u}ᵒᵖ) :
    TrackInterchange ((ParameterModels.supportedOpenNull f).homotopy X)
      ((ParameterModels.supportedOpenNull f).homotopy (laurent.op.obj X))
      ((supportedTrack f).homotopy X) ((openTrack f).homotopy X) :=
  ParameterLaurentNull.supportedOpenNull_laurentInterchange f X
