module
import Colib.AlgebraicGeometry.KTheory.PerfectSupportedPairPullback
import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenCoarsePullback

open CategoryTheory AlgebraicGeometry
universe u
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
section
variable {A B C : Scheme.QuasiCompactOpenPairs.{u}}

example (f : A ⟶ B) (n : ℕ) :
    (perfectSupportedKPullback f n).comp (boundedAboveFlatPerfectSupportedToPerfectKMap
      B.obj.hom n) =
      (boundedAboveFlatPerfectSupportedToPerfectKMap A.obj.hom n).comp
        (boundedAboveFlatPerfectSupportedKPullback f.hom n) :=
  perfectSupportedKPullback_comp_boundedFlat f n

example (A :
  AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}) (n : ℕ)
  :
    perfectSupportedKPullback (𝟙 A) n = MonoidHom.id _ := perfectSupportedKPullback_id A n

end
section
variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.right = g ≫ j)
variable [CompactSpace X'] [CompactSpace X]

example (n : ℕ) :
    (perfectSupportedOpenKPullback j' j f g w n).comp
        (boundedAboveFlatPerfectSupportedOpenToPerfectKMap j T n) =
      (boundedAboveFlatPerfectSupportedOpenToPerfectKMap j' S n).comp
        (boundedAboveFlatPerfectSupportedOpenKPullback j' j f g w n) :=
  perfectSupportedOpenKPullback_comp_boundedFlat j' j f g w n

end
end AlgebraicGeometry.Scheme.Modules
