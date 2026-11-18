module

public import Colib.AlgebraicGeometry.KTheory.PerfectOpenKZeroImage

set_option autoImplicit false

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

example :
    PerfectOpenK j 0 ⧸ (perfectOpenKZeroToImage j).ker ≃* PerfectOpenKZeroImage j :=
  perfectOpenKZeroQuotientImageEquiv j

example (a : PerfectOpenK j 0) :
    (perfectOpenKZeroQuotientImageEquiv j (QuotientGroup.mk a) :
      (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K 0) =
        perfectOpenKRestrict j 0 a :=
  perfectOpenKZeroQuotientImageEquiv_mk j a

example :
    Function.Surjective (perfectOpenKRestrict j 0) ↔
      Function.Surjective (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0) :=
  perfectOpenKRestrict_zero_surjective_iff j

end
