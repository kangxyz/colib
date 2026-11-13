module
import Colib.AlgebraicGeometry.KTheory.PerfectOpenImagePullback
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.AlgebraicGrothendieck
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
variable {U X U' X' : Scheme.{u}} [CompactSpace U] [CompactSpace X]
  [CompactSpace U'] [CompactSpace X']
  (j : U ⟶ X) (j' : U' ⟶ X') [IsOpenImmersion j] [IsOpenImmersion j']
  (p : X' ⟶ X) (q : U' ⟶ U) (h : q ≫ j = j' ≫ p)
example :
    (perfectGrothendieckPullback q).comp
      (map (perfectComplexesWaldhausen X.toRingedSpace) (perfectComplexesRestrictOpenImmersion j)
        (perfectComplexesRestrictOpenImmersion_isExact j)) =
    (map (perfectComplexesWaldhausen X'.toRingedSpace) (perfectComplexesRestrictOpenImmersion j')
      (perfectComplexesRestrictOpenImmersion_isExact j')).comp
      (perfectGrothendieckPullback p) :=
  perfectGrothendieckPullback_restrictionSquare j j' p q h
example (x : Group (perfectComplexesWaldhausen
  U.toRingedSpace)) :
    perfectOpenImageQuotientPullback j j' p q h
      (QuotientAddGroup.mk' (map (perfectOpenWeakWaldhausen j)
        (perfectComplexesRestrictOpenImmersion j)
        (perfectOpenRestrict_isExact j)).range x) =
    QuotientAddGroup.mk' (map (perfectOpenWeakWaldhausen j')
      (perfectComplexesRestrictOpenImmersion j')
      (perfectOpenRestrict_isExact j')).range (perfectGrothendieckPullback q x) :=
  perfectOpenImageQuotientPullback_mk j j' p q h x
example (K :
  (boundedAboveFlatPerfectComplex U.toRingedSpace).FullSubcategory) :
    perfectOpenImageQuotientPullback j j' p q h
      ((imageQuotientGrading (perfectOpenWeakWaldhausen j) (perfectComplexesRestrictOpenImmersion j)
        (perfectOpenRestrict_isExact j)).value ((boundedAboveFlatPerfectInclusion
          U.toRingedSpace).obj K)) =
    (imageQuotientGrading (perfectOpenWeakWaldhausen j') (perfectComplexesRestrictOpenImmersion j')
      (perfectOpenRestrict_isExact j')).value
        ((boundedAboveFlatPerfectInclusion U'.toRingedSpace).obj ((boundedAboveFlatPerfectPullback
          q).obj K)) :=
  perfectOpenImageQuotientPullback_boundedFlat_objectClass j j' p q h K
