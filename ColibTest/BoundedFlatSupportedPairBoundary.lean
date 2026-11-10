/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedBoundaryNaturality

/-! The original supported maps, restriction and boundary for arbitrary commuting pairs. -/
noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules

universe u
variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.right = g ≫ j)

example (n : ℕ) :
    (BoundedAboveFlatPerfectSupportedKFunctor n).map f.op =
      GrpCat.ofHom (boundedAboveFlatPerfectSupportedKPullback f n) := rfl

example :
    (supportedPairUnionSquare j' j f g w).right = f.right := rfl

example :
    (supportedPairTargetSquare j' j f g w).right = g := rfl

example :
    IsExact (boundedAboveFlatPerfectSupportedOpenWaldhausen j T).cof
      (boundedAboveFlatPerfectSupportedOpenWaldhausen j T).weq
      (boundedAboveFlatPerfectSupportedOpenWaldhausen j' S).cof
      (boundedAboveFlatPerfectSupportedOpenWaldhausen j' S).weq
      (boundedAboveFlatPerfectSupportedPullback f) :=
  boundedAboveFlatPerfectSupportedOpenPullback_isExact j' j f g w

example :
    (boundedAboveFlatPerfectSupportedOpenKPullback j' j f g w 0).comp
        (boundedAboveFlatPerfectSupportedOpenKMap j T 0) =
      (boundedAboveFlatPerfectSupportedOpenKMap j' S 0).comp
        (boundedAboveFlatPerfectSupportedKPullback f 0) :=
  boundedAboveFlatPerfectSupportedOpenKPullback_changeWeak j' j f g w 0

example :
    (boundedAboveFlatPerfectSupportedKPullback (supportedPairTargetSquare j' j f g w) 0).comp
        (boundedAboveFlatPerfectSupportedOpenKRestrict j 0) =
      (boundedAboveFlatPerfectSupportedOpenKRestrict j' 0).comp
        (boundedAboveFlatPerfectSupportedOpenKPullback j' j f g w 0) :=
  boundedAboveFlatPerfectSupportedOpenKRestrict_pullback j' j f g w 0

example (n : ℕ) :
    (boundedAboveFlatPerfectSupportedKPullback (supportedPairUnionSquare j' j f g w) n).comp
        (boundedAboveFlatPerfectSupportedOpenConnectingHom j T n) =
      (boundedAboveFlatPerfectSupportedOpenConnectingHom j' S n).comp
        (boundedAboveFlatPerfectSupportedOpenKPullback j' j f g w (n + 1)) :=
  boundedAboveFlatPerfectSupportedOpenConnectingHom_pullback j' j f g w n

example :
    (boundedAboveFlatPerfectSupportedKPullback (supportedPairUnionSquare j' j f g w) 0).comp
        (boundedAboveFlatPerfectSupportedOpenConnectingHom j T 0) =
      (boundedAboveFlatPerfectSupportedOpenConnectingHom j' S 0).comp
        (boundedAboveFlatPerfectSupportedOpenKPullback j' j f g w 1) :=
  boundedAboveFlatPerfectSupportedOpenConnectingHom_pullback j' j f g w 0
