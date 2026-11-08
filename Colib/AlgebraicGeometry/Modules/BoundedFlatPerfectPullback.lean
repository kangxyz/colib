/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullbackBasic
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectWaldhausen
public import Colib.AlgebraicGeometry.Modules.PullbackFlatQuotient

/-! # Actual exact and Waldhausen pullback on bounded-above flat perfect complexes -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Termwise geometric pullback on the actual full chain subcategory. -/
def boundedAboveFlatPerfectPullback (f : X ⟶ Y) :
    (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory ⥤
      (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory :=
  (boundedAboveFlatPerfectComplex X.toRingedSpace).lift
    ((boundedAboveFlatPerfectComplex Y.toRingedSpace).ι ⋙
      (pullback f).mapHomologicalComplex (ComplexShape.up ℤ))
    (fun K => boundedAboveFlatPerfectComplex_pullback f K.property)

instance boundedAboveFlatPerfectPullback_additive (f : X ⟶ Y) :
    (boundedAboveFlatPerfectPullback f).Additive := by
  dsimp [boundedAboveFlatPerfectPullback]
  infer_instance

/-- Every inherited conflation pulls back to a conflation, using its actual flat quotient. -/
def boundedAboveFlatPerfectExactPullback (f : X ⟶ Y) :
    ExactFunctor (boundedAboveFlatPerfectExactStructure Y.toRingedSpace)
      (boundedAboveFlatPerfectExactStructure X.toRingedSpace) where
  toFunctor := boundedAboveFlatPerfectPullback f
  map_conflation S hS := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    exact shortExact_pullback_of_flat_quotient f
      ((S.map (boundedAboveFlatPerfectComplex Y.toRingedSpace).ι).map
        (HomologicalComplex.eval Y.Modules (ComplexShape.up ℤ) n))
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 hS n)
      (S.X₃.property.2.2 n)

/-- Arbitrary pullback is Waldhausen exact for admissible quotients and quasi-isomorphisms. -/
@[colib_tag "COL-0326",
  colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/Pullback.lean:62-75"
    "adaptation" "Actual arbitrary chain pullback with inherited flat-quotient conflations"]
theorem boundedAboveFlatPerfectPullback_isExact (f : X ⟶ Y) :
    Waldhausen.IsExact (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).weq
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq
      (boundedAboveFlatPerfectPullback f) where
  zero h := (boundedAboveFlatPerfectPullback f).map_isZero h
  cofibration s hs := (boundedAboveFlatPerfectExactPullback f).map_inflation s hs
  weak {K L} s hs := by
    let : QuasiIso s.hom := hs
    exact quasiIso_pullback_of_boundedAboveFlatPerfect f K.property L.property s.hom
  pushout hi h := (boundedAboveFlatPerfectExactPullback f).map_isPushout hi h

end AlgebraicGeometry.Scheme.Modules
