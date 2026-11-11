module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenKRestriction
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)
example : BoundedAboveFlatPerfectOpenK j n →*
    RingedSpace.boundedAboveFlatPerfectK U.toRingedSpace n :=
  boundedAboveFlatPerfectOpenKRestrict j n
example :
    (perfectOpenKRestrict j n).comp (boundedAboveFlatPerfectOpenToPerfectOpenKMap j n) =
      (RingedSpace.boundedAboveFlatPerfectToPerfectKMap U.toRingedSpace n).comp
        (boundedAboveFlatPerfectOpenKRestrict j n) :=
  boundedAboveFlatPerfectOpenKRestrict_comparison j n
