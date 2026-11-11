module
import Colib.AlgebraicGeometry.KTheory.PerfectSupportedGrothendieckPullback
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.AlgebraicGrothendieck
universe u
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
variable {A B C : Scheme.QuasiCompactOpenPairs.{u}}
example (f : A ⟶ B) (g : B ⟶ C) :
    perfectSupportedGrothendieckPullback (f ≫ g) =
      (perfectSupportedGrothendieckPullback f).comp (perfectSupportedGrothendieckPullback g) :=
  perfectSupportedGrothendieckPullback_comp f g
example (f : A ⟶ B) (x : Group (perfectSupportedWaldhausen B.obj.hom)) :
    perfectSupportedGrothendieckKZeroEquiv A.obj.hom
        (Multiplicative.ofAdd (perfectSupportedGrothendieckPullback f x)) =
      perfectSupportedKPullback f 0
        (perfectSupportedGrothendieckKZeroEquiv B.obj.hom (Multiplicative.ofAdd x)) :=
  perfectSupportedGrothendieckPullback_comparison f x
variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.right = g ≫ j) [CompactSpace X'] [CompactSpace X]
example (x : Group (perfectSupportedOpenWeakWaldhausen j T)) :
    perfectSupportedOpenGrothendieckKZeroEquiv j' S
        (Multiplicative.ofAdd (perfectSupportedOpenGrothendieckPullback j' j f g w x)) =
      perfectSupportedOpenKPullback j' j f g w 0
        (perfectSupportedOpenGrothendieckKZeroEquiv j T (Multiplicative.ofAdd x)) :=
  perfectSupportedOpenGrothendieckPullback_comparison j' j f g w x
example [CompactSpace U'] [CompactSpace U] :
    (perfectSupportedGrothendieckPullback
      (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w))).comp
        (map (perfectSupportedOpenWeakWaldhausen j T) (perfectSupportedRestrict j T)
          (perfectSupportedOpenRestrict_waldhausenExact j T)) =
      (map (perfectSupportedOpenWeakWaldhausen j' S) (perfectSupportedRestrict j' S)
        (perfectSupportedOpenRestrict_waldhausenExact j' S)).comp
          (perfectSupportedOpenGrothendieckPullback j' j f g w) :=
  perfectSupportedOpenGrothendieckPullback_restrictionSquare j' j f g w
end AlgebraicGeometry.Scheme.Modules
