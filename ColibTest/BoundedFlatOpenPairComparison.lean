/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenComparison

/-! The genuine relative replacement and original forward inclusion, including K-zero. -/
noncomputable section
open CategoryTheory CategoryTheory.Waldhausen
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace

universe u
attribute [local instance] Abelian.hasFiniteBiproducts
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [CompactSpace X]

example (n : ℕ) :
    Function.Bijective (KMap (boundedAboveFlatPerfectOpenInclusion_isExact j) n) :=
  boundedAboveFlatPerfectOpenToPerfectOpenKMap_bijective j n

example :
    (↑(boundedAboveFlatPerfectOpenKEquiv j 0) :
      BoundedAboveFlatPerfectOpenK j 0 →* PerfectOpenK j 0) =
      KMap (boundedAboveFlatPerfectOpenInclusion_isExact j) 0 := rfl

example (n : ℕ) :
    (boundedAboveFlatPerfectOpenToPerfectOpenKMap j n).comp
        (boundedAboveFlatPerfectOpenKMap j n) =
      (perfectOpenKMap j n).comp (boundedAboveFlatPerfectToPerfectKMap X.toRingedSpace n) :=
  boundedAboveFlatPerfectOpenToPerfectOpenKMap_changeWeak j n

example {K : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory}
    {L : ObjectProperty.FullSubcategory (IsPerfectComplex (X := X.toRingedSpace))}
    (f : (boundedAboveFlatPerfectInclusion X.toRingedSpace).obj K ⟶ L) :
    ∃ (M : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory) (i : K ⟶ M)
      (p : (boundedAboveFlatPerfectInclusion X.toRingedSpace).obj M ⟶ L),
      (boundedAboveFlatPerfectOpenWaldhausen j).cof i ∧
      (perfectOpenWeakWaldhausen j).weq p ∧
      (boundedAboveFlatPerfectInclusion X.toRingedSpace).map i ≫ p = f :=
  (boundedAboveFlatPerfectOpenInclusion_approximation j).lift f
