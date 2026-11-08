/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullbackCoherence
public import Colib.AlgebraicGeometry.KTheory.BoundedFiniteLocallyFreeFlat
public import Colib.AlgebraicGeometry.KTheory.BoundedFiniteLocallyFreePullback

/-!
# Actual K-pullback of bounded-above flat perfect complexes

These are the canonical normalized KMaps of actual exact functors. All equations hold in
every connective degree, including zero, without compactness or flatness of the morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

/-- The canonical K-map of the actual bounded-flat chain pullback. -/
@[colib_tag "COL-0326",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/Functor.lean:47-64"
    "adaptation" "Canonical normalized KMap of the actual bounded-above flat chain pullback"]
def boundedAboveFlatPerfectKPullback (f : X ⟶ Y) (n : ℕ) :
    Y.toRingedSpace.boundedAboveFlatPerfectK n →* X.toRingedSpace.boundedAboveFlatPerfectK n :=
  Waldhausen.KMap (boundedAboveFlatPerfectPullback_isExact f) n

@[simp]
theorem boundedAboveFlatPerfectKPullback_id (X : Scheme.{u}) (n : ℕ) :
    boundedAboveFlatPerfectKPullback (𝟙 X) n =
      MonoidHom.id (X.toRingedSpace.boundedAboveFlatPerfectK n) :=
  (Waldhausen.KMap_eq_of_iso (boundedAboveFlatPerfectPullback_isExact (𝟙 X))
    (Waldhausen.IsExact.id (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq)
    (boundedAboveFlatPerfectPullbackIdIso X) n).trans (Waldhausen.KMap_id _ n)

@[simp]
theorem boundedAboveFlatPerfectKPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    boundedAboveFlatPerfectKPullback (f ≫ g) n =
      (boundedAboveFlatPerfectKPullback f n).comp (boundedAboveFlatPerfectKPullback g n) :=
  (Waldhausen.KMap_eq_of_iso (boundedAboveFlatPerfectPullback_isExact (f ≫ g))
    ((boundedAboveFlatPerfectPullback_isExact g).comp (boundedAboveFlatPerfectPullback_isExact f))
    (boundedAboveFlatPerfectPullbackCompIso f g) n).trans
    (Waldhausen.KMap_comp_KMap (boundedAboveFlatPerfectPullback_isExact g)
      (boundedAboveFlatPerfectPullback_isExact f) n).symm

/-- The literal bounded-vector-bundle-to-flat map commutes with arbitrary K-pullback. -/
theorem boundedFiniteLocallyFreeToFlatKMap_pullback (f : X ⟶ Y) (n : ℕ) :
    (boundedAboveFlatPerfectKPullback f n).comp (boundedFiniteLocallyFreeToFlatKMap Y n) =
      (boundedFiniteLocallyFreeToFlatKMap X n).comp (boundedFiniteLocallyFreeKPullback f n) := by
  unfold boundedAboveFlatPerfectKPullback boundedFiniteLocallyFreeToFlatKMap
    boundedFiniteLocallyFreeKPullback
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]
  exact Waldhausen.KMap_eq_of_iso _ _ (boundedFiniteLocallyFreeFlatInclusionPullbackIso f) n

end AlgebraicGeometry.Scheme
