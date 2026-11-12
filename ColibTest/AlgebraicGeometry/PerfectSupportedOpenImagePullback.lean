module
import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenImagePullback
noncomputable section
open CategoryTheory.Waldhausen
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen.AlgebraicGrothendieck
universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
variable {U' X' : Scheme.{u}} (j' : U' ⟶ X') [IsOpenImmersion j'] {S : X'.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.right = g ≫ j)
  [CompactSpace X'] [CompactSpace X] [CompactSpace U'] [CompactSpace U]

example :
    (map (perfectSupportedOpenWeakWaldhausen j T) (perfectSupportedRestrict j T)
      (perfectSupportedOpenRestrict_waldhausenExact j T)).range ≤
    (map (perfectSupportedOpenWeakWaldhausen j' S) (perfectSupportedRestrict j' S)
      (perfectSupportedOpenRestrict_waldhausenExact j' S)).range.comap
        (perfectSupportedGrothendieckPullback
          (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w)))  :=
  perfectSupportedOpenImagePullback_range_le j T j' f g w

example
    (K : (boundedAboveFlatPerfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory) :
    perfectSupportedOpenImageQuotientPullback j T j' f g w
      ((perfectSupportedOpenDeficitGrading j T).value
        ((boundedAboveFlatPerfectSupportedInclusion (j ⁻¹ᵁ T).ι).obj K)) =
    (perfectSupportedOpenDeficitGrading j' S).value
      ((boundedAboveFlatPerfectSupportedInclusion (j' ⁻¹ᵁ S).ι).obj
        ((boundedAboveFlatPerfectSupportedPullback (supportedPairTargetSquare j' j f g w)).obj
    K))  :=
  perfectSupportedOpenImageQuotientPullback_boundedFlat_objectClass j T j' f g w K

end AlgebraicGeometry.Scheme.Modules
