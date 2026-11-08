/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectPullbackCompatibility

/-! # Full-signature consumers for literal perfect pullback compatibility -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules

universe u

example {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    boundedAboveFlatPerfectInclusion Y.toRingedSpace ⋙ perfectFlatPullback f ≅
      boundedAboveFlatPerfectPullback f ⋙ boundedAboveFlatPerfectInclusion X.toRingedSpace :=
  boundedAboveFlatPerfectInclusionFlatPullbackIso f

example {X Y : Scheme.{u}} [CompactSpace Y] (f : X ⟶ Y) [Flat f] (n : ℕ) :
    perfectKPullback f n = Waldhausen.KMap (perfectFlatPullback_waldhausenExact f) n :=
  perfectKPullback_eq_flatPullback f n

example {X Y : Scheme.{u}} [CompactSpace Y] (f : X ⟶ Y) [Flat f] :
    perfectKPullback f 0 = Waldhausen.KMap (perfectFlatPullback_waldhausenExact f) 0 :=
  perfectKPullback_eq_flatPullback f 0

example {X Y : Scheme.{u}} [CompactSpace Y] (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ) :
    perfectKPullback j n =
      Waldhausen.KMap (perfectComplexesRestrictOpenImmersion_isExact j) n :=
  perfectKPullback_eq_restrict j n

example (X : Scheme.{u}) [CompactSpace X] (U : X.Opens) :
    perfectKPullback U.ι 0 = perfectComplexesRestrictKMap X U 0 :=
  perfectKPullback_eq_restrictSubset X U 0

example {X Y : Scheme.{u}} [CompactSpace Y] (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ) :
    (perfectOpenKRestrict j n).comp (perfectOpenKMap j n) = perfectKPullback j n :=
  perfectOpenKRestrict_comp_eq_perfectKPullback j n

example (X : Scheme.{u}) [CompactSpace X] (n : ℕ) :
    Waldhausen.KMap (perfectFlatPullback_waldhausenExact (𝟙 X)) n =
      MonoidHom.id ((perfectComplexesWaldhausen X.toRingedSpace).K n) := by
  rw [← perfectKPullback_eq_flatPullback, perfectKPullback_id]

example {X Y Z : Scheme.{u}} [CompactSpace Z] (f : X ⟶ Y) [Flat f]
    (g : Y ⟶ Z) (n : ℕ) :
    perfectKPullback (f ≫ g) n =
      (Waldhausen.KMap (perfectFlatPullback_waldhausenExact f) n).comp
        (perfectKPullback g n) :=
  perfectKPullback_comp_flatLeft f g n

example {U V X Y : Scheme.{u}} [CompactSpace Y] [CompactSpace V]
    (j : U ⟶ X) (k : V ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion k]
    (f : X ⟶ Y) (g : U ⟶ V) (h : j ≫ f = g ≫ k) (n : ℕ) :
    (Waldhausen.KMap (perfectComplexesRestrictOpenImmersion_isExact j) n).comp
        (perfectKPullback f n) =
      (perfectKPullback g n).comp
        (Waldhausen.KMap (perfectComplexesRestrictOpenImmersion_isExact k) n) :=
  perfectKPullback_restrict_square j k f g h n

example {U V X Y : Scheme.{u}} [CompactSpace Y] [CompactSpace V]
    (j : U ⟶ X) (k : V ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion k]
    (f : X ⟶ Y) (g : U ⟶ V) (h : j ≫ f = g ≫ k) :
    (Waldhausen.KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0).comp
        (perfectKPullback f 0) =
      (perfectKPullback g 0).comp
        (Waldhausen.KMap (perfectComplexesRestrictOpenImmersion_isExact k) 0) :=
  perfectKPullback_restrict_square j k f g h 0
