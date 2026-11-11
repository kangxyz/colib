module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullTwistedNull
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryTwistedNull
open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum KTheory.Bass
open KTheory.Bass.SchemeNaturalSeed KTheory.Bass.NaturalTrack
universe u
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
open ParameterLaurentTrack
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
example (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((normalizedTelescope (supportedTrack f)).obj X).space n) :
    ((conjugacyTelescopeMap (ambientTrack P)).app X).map n
      (((normalizedNull f).homotopy X).level n (r, x)) =
      ((twistedNull f).homotopy X).level n
        (r, ((conjugacyTelescopeMap (supportedTrack f)).app X).map n x) :=
  twisted_null_square f X n r x
end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)
example (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((normalizedTelescope (fiberAction f T)).obj X).space n) :
    ((conjugacyTelescopeMap (openAction f T)).app X).map n
      (((normalizedNull f T).homotopy X).level n (r, x)) =
      ((twistedNull f T).homotopy X).level n
        (r, ((conjugacyTelescopeMap (fiberAction f T)).app X).map n x) :=
  twisted_null_square f T X n r x
end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
