module
import Colib.AlgebraicGeometry.KTheory.PerfectOpenDeficitGrading
open CategoryTheory AlgebraicGeometry CategoryTheory.Waldhausen
open AlgebraicGeometry.Scheme.Modules CategoryTheory.Waldhausen.AlgebraicGrothendieck
noncomputable section
universe u
example {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    perfectOpenDeficitGrading j =
      imageQuotientGrading (perfectOpenWeakWaldhausen j)
        (perfectComplexesRestrictOpenImmersion j) (perfectOpenRestrict_isExact j) := rfl
