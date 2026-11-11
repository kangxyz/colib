module
import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterAuxiliarySupportTrack
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex KTheory.Bass
universe u
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
open ParameterLaurentTrack NaturalTrack
example {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) (X : Scheme.{u}ᵒᵖ) :
    Preserves ((supportedMap g).app (laurent.op.obj X)).hom.toFunctor
      (supportedUnit B.hom X) (supportedUnit A.hom X) := supportedMap_unit g X
example {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) :
    Equivariant (supportedTrack B.hom) (supportedTrack A.hom)
      (Functor.whiskerRight (supportedMap g) prespectrumFunctor) := supportedMap_equivariant g
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)
example : Equivariant (supportedTrack (unionOpen f T).ι) (supportedTrack T.ι)
    (Functor.whiskerRight (enlargement f T) prespectrumFunctor) := enlargement_equivariant f T
omit [IsOpenImmersion f] in
example : Equivariant (supportedTrack T.ι) (supportedTrack (inverseOpen f T).ι)
    (Functor.whiskerRight (restriction f T) prespectrumFunctor) := restriction_equivariant f T
end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
