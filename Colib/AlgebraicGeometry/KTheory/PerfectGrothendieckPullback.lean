/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectPullbackCompatibility
public import Colib.AlgebraicGeometry.KTheory.PerfectGrothendieckComparison

/-!
# Original derived pullback on perfect-complex Grothendieck groups

The homomorphism transports the existing `perfectKPullback` through the genuine
original Grothendieck comparisons. It is not an assertion of an exact raw
perfect pullback functor. Its bounded-flat formula retains the actual geometric
pullback on representatives, without a flatness assumption on the scheme map.
-/
@[expose] public section

open AlgebraicGeometry.RingedSpace

open CategoryTheory.Waldhausen


noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen.AlgebraicGrothendieck
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Transport of the actual derived K-zero pullback through the original comparisons. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/GrothendieckPullback.lean:33"
  "adaptation" "Original derived Grothendieck pullback through actual K comparison"]
def perfectGrothendieckPullback {X Y : Scheme.{u}} [CompactSpace Y]
    (f : X ⟶ Y) : Group (perfectComplexesWaldhausen Y.toRingedSpace) →+ Group
      (perfectComplexesWaldhausen X.toRingedSpace) :=
  ((perfectGrothendieckKZeroEquiv X).symm.toMonoidHom.comp
    ((perfectKPullback f 0).comp (perfectGrothendieckKZeroEquiv Y).toMonoidHom)).toAdditive

/-- The original comparison square holds on every original algebraic class. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/GrothendieckPullback.lean:39"
  "adaptation" "Original derived Grothendieck pullback through actual K comparison"]
theorem perfectGrothendieckPullback_comparison {X Y : Scheme.{u}}
    [CompactSpace Y] (f : X ⟶ Y) (x : Group (perfectComplexesWaldhausen
      Y.toRingedSpace)) :
    perfectGrothendieckKZeroEquiv X (Multiplicative.ofAdd (perfectGrothendieckPullback f x)) =
      perfectKPullback f 0 (perfectGrothendieckKZeroEquiv Y (Multiplicative.ofAdd x)) :=
  (perfectGrothendieckKZeroEquiv X).apply_symm_apply _

/-- Composition retains the original derived K-map composition, with its contravariant order. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/GrothendieckPullback.lean:46"
  "adaptation" "Original derived Grothendieck pullback through actual K comparison"]
theorem perfectGrothendieckPullback_comp {X Y Z : Scheme.{u}}
    [CompactSpace Y] [CompactSpace Z] (f : X ⟶ Y) (g : Y ⟶ Z) :
    perfectGrothendieckPullback (f ≫ g) =
      (perfectGrothendieckPullback f).comp (perfectGrothendieckPullback g) := by
  apply AddMonoidHom.ext
  intro x
  apply (perfectGrothendieckKZeroEquiv X).injective
  change perfectGrothendieckKZeroEquiv X
      (Multiplicative.ofAdd (perfectGrothendieckPullback (f ≫ g) x)) =
    perfectGrothendieckKZeroEquiv X
      (Multiplicative.ofAdd (perfectGrothendieckPullback f (perfectGrothendieckPullback g x)))
  rw [perfectGrothendieckPullback_comparison, perfectGrothendieckPullback_comparison,
    perfectGrothendieckPullback_comparison, perfectKPullback_comp]
  rfl

/-- On an actual open immersion this is the unchanged original algebraic restriction map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/GrothendieckPullback.lean:62"
  "adaptation" "Original derived Grothendieck pullback through actual K comparison"]
theorem perfectGrothendieckPullback_restrict {U X : Scheme.{u}}
    [CompactSpace X] (j : U ⟶ X) [IsOpenImmersion j] :
    perfectGrothendieckPullback j =
      map (perfectComplexesWaldhausen X.toRingedSpace) (perfectComplexesRestrictOpenImmersion j)
        (perfectComplexesRestrictOpenImmersion_isExact j) := by
  apply AddMonoidHom.ext
  intro x
  apply (perfectGrothendieckKZeroEquiv U).injective
  change perfectGrothendieckKZeroEquiv U
    (Multiplicative.ofAdd (perfectGrothendieckPullback j x)) = _
  rw [perfectGrothendieckPullback_comparison, perfectKPullback_eq_restrict]
  exact perfectGrothendieckKZeroEquiv_restrict j (Multiplicative.ofAdd x)

/-- An original bounded-flat representative is pulled back by the genuine termwise functor. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/GrothendieckPullback.lean:75"
  "adaptation" "Original derived Grothendieck pullback through actual K comparison"]
theorem perfectGrothendieckPullback_boundedFlat_objectClass {X Y : Scheme.{u}}
    [CompactSpace Y] (f : X ⟶ Y) (K : (boundedAboveFlatPerfectComplex
      Y.toRingedSpace).FullSubcategory) :
    perfectGrothendieckPullback f
      (objectClass (perfectComplexesWaldhausen Y.toRingedSpace) ((boundedAboveFlatPerfectInclusion
        Y.toRingedSpace).obj K)) =
    objectClass (perfectComplexesWaldhausen X.toRingedSpace)
      ((boundedAboveFlatPerfectInclusion X.toRingedSpace).obj ((boundedAboveFlatPerfectPullback
        f).obj K)) := by
  apply (perfectGrothendieckKZeroEquiv X).injective
  change perfectGrothendieckKZeroEquiv X
      (Multiplicative.ofAdd (perfectGrothendieckPullback f
        (objectClass (perfectComplexesWaldhausen Y.toRingedSpace)
          ((boundedAboveFlatPerfectInclusion Y.toRingedSpace).obj K)))) =
    perfectGrothendieckKZeroEquiv X
      (Multiplicative.ofAdd (objectClass (perfectComplexesWaldhausen X.toRingedSpace)
        ((boundedAboveFlatPerfectInclusion X.toRingedSpace).obj ((boundedAboveFlatPerfectPullback
          f).obj K))))
  rw [perfectGrothendieckPullback_comparison, perfectGrothendieckKZeroEquiv_objectClass,
    perfectGrothendieckKZeroEquiv_objectClass]
  have h := DFunLike.congr_fun (boundedAboveFlatPerfectToPerfectKMap_pullback f 0)
    ((boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).kZeroObjectClass K)
  change perfectKPullback f 0
      (KMap (boundedAboveFlatPerfectInclusion_isExact Y.toRingedSpace) 0
        ((boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).kZeroObjectClass K)) =
    KMap (boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace) 0
      (KMap (boundedAboveFlatPerfectPullback_isExact f) 0
        ((boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).kZeroObjectClass K)) at h
  rw [KMap_kZeroObjectClass, KMap_kZeroObjectClass, KMap_kZeroObjectClass] at h
  exact h

end AlgebraicGeometry.Scheme.Modules
