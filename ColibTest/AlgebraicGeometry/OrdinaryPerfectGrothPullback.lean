module
import Colib.AlgebraicGeometry.KTheory.PerfectGrothendieckPullback
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.AlgebraicGrothendieck
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
example {X Y Z : Scheme.{u}} [CompactSpace X] [CompactSpace Y] [CompactSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) : perfectGrothendieckPullback (f ≫ g) =
      (perfectGrothendieckPullback f).comp (perfectGrothendieckPullback g) :=
  perfectGrothendieckPullback_comp f g
example {U X : Scheme.{u}} [CompactSpace U] [CompactSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] : perfectGrothendieckPullback j =
      map (perfectComplexesWaldhausen X.toRingedSpace)
        (perfectComplexesRestrictOpenImmersion j)
        (perfectComplexesRestrictOpenImmersion_isExact j) :=
  perfectGrothendieckPullback_restrict j
example {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y] (f : X ⟶ Y)
    (K : (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory) :
    perfectGrothendieckPullback f
      (objectClass (perfectComplexesWaldhausen Y.toRingedSpace)
        ((boundedAboveFlatPerfectInclusion Y.toRingedSpace).obj K)) =
      objectClass (perfectComplexesWaldhausen X.toRingedSpace)
        ((boundedAboveFlatPerfectInclusion X.toRingedSpace).obj
          ((boundedAboveFlatPerfectPullback f).obj K)) :=
  perfectGrothendieckPullback_boundedFlat_objectClass f K
