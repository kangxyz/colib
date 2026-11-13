module
import Colib.AlgebraicGeometry.KTheory.PerfectGrothendieckComparison
open CategoryTheory AlgebraicGeometry CategoryTheory.Waldhausen
open AlgebraicGeometry.Scheme.Modules CategoryTheory.Waldhausen.AlgebraicGrothendieck
noncomputable section
universe u
example (X : Scheme.{u})
    (A : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    perfectGrothendieckKZeroEquiv X
      (Multiplicative.ofAdd
        (objectClass (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace) A)) =
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kZeroObjectClass A :=
  perfectGrothendieckKZeroEquiv_objectClass X A
example {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (a : Multiplicative (Group (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))) :
    KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0
        (perfectGrothendieckKZeroEquiv X a) =
      perfectGrothendieckKZeroEquiv U
        ((map (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
          (perfectComplexesRestrictOpenImmersion j)
          (perfectComplexesRestrictOpenImmersion_isExact j)).toMultiplicative a) :=
  perfectGrothendieckKZeroEquiv_restrict j a
