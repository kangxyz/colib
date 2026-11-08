/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.PerfectPullbackFunctor

/-! # Full-signature consumers of actual flat and perfect K-pullback -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

variable {X Y Z : Scheme.{u}}

example (f : X ⟶ Y) (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat (O := Y.sheaf) S.X₃) :
    (S.map (Scheme.Modules.pullback f)).ShortExact :=
  shortExact_pullback_of_flat_quotient f S hS hflat

example {K : CochainComplex Y.Modules ℤ}
    (hK : boundedAboveFlatPerfectComplex Y.toRingedSpace K) :
    RingedSpace.KFlatDerivedPullback.KFlat Y.toRingedSpace K :=
  kFlat_of_boundedAboveFlatPerfect hK

example (f : X ⟶ Y) {K : CochainComplex Y.Modules ℤ}
    (hK : boundedAboveFlatPerfectComplex Y.toRingedSpace K) :
    boundedAboveFlatPerfectComplex X.toRingedSpace
      (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  boundedAboveFlatPerfectComplex_pullback f hK

example (f : X ⟶ Y) {K L : CochainComplex Y.Modules ℤ}
    (hK : boundedAboveFlatPerfectComplex Y.toRingedSpace K)
    (hL : boundedAboveFlatPerfectComplex Y.toRingedSpace L) (s : K ⟶ L) [QuasiIso s] :
    QuasiIso (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map s) :=
  quasiIso_pullback_of_boundedAboveFlatPerfect f hK hL s

example (f : X ⟶ Y) :
    ExactFunctor (boundedAboveFlatPerfectExactStructure Y.toRingedSpace)
      (boundedAboveFlatPerfectExactStructure X.toRingedSpace) :=
  boundedAboveFlatPerfectExactPullback f

example (f : X ⟶ Y) :
    Waldhausen.IsExact (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).weq
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq
      (boundedAboveFlatPerfectPullback f) := boundedAboveFlatPerfectPullback_isExact f

example (X : Scheme.{u}) :
    boundedAboveFlatPerfectPullback (𝟙 X) ≅
      𝟭 (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory :=
  boundedAboveFlatPerfectPullbackIdIso X

example (f : X ⟶ Y) (g : Y ⟶ Z) :
    boundedAboveFlatPerfectPullback (f ≫ g) ≅
      boundedAboveFlatPerfectPullback g ⋙ boundedAboveFlatPerfectPullback f :=
  boundedAboveFlatPerfectPullbackCompIso f g

example (f : X ⟶ Y) :
    boundedFiniteLocallyFreeFlatInclusion Y ⋙ boundedAboveFlatPerfectPullback f ≅
      boundedFiniteLocallyFreePullback f ⋙ boundedFiniteLocallyFreeFlatInclusion X :=
  boundedFiniteLocallyFreeFlatInclusionPullbackIso f

example (f : X ⟶ Y) (n : ℕ) :
    boundedAboveFlatPerfectKPullback f n =
      Waldhausen.KMap (boundedAboveFlatPerfectPullback_isExact f) n := rfl

example (f : X ⟶ Y) :
    boundedAboveFlatPerfectKPullback f 0 =
      Waldhausen.KMap (boundedAboveFlatPerfectPullback_isExact f) 0 := rfl

example (X : Scheme.{u}) (n : ℕ) :
    boundedAboveFlatPerfectKPullback (𝟙 X) n =
      MonoidHom.id (X.toRingedSpace.boundedAboveFlatPerfectK n) :=
  boundedAboveFlatPerfectKPullback_id X n

example (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    boundedAboveFlatPerfectKPullback (f ≫ g) n =
      (boundedAboveFlatPerfectKPullback f n).comp (boundedAboveFlatPerfectKPullback g n) :=
  boundedAboveFlatPerfectKPullback_comp f g n

example (f : X ⟶ Y) [CompactSpace Y] (n : ℕ) :
    (perfectComplexesWaldhausen Y.toRingedSpace).K n →*
      (perfectComplexesWaldhausen X.toRingedSpace).K n := perfectKPullback f n

example (f : X ⟶ Y) [CompactSpace Y] :
    (perfectComplexesWaldhausen Y.toRingedSpace).K 0 →*
      (perfectComplexesWaldhausen X.toRingedSpace).K 0 := perfectKPullback f 0

example (f : X ⟶ Y) [CompactSpace Y] (n : ℕ) :
    (perfectKPullback f n).comp (boundedAboveFlatPerfectToPerfectKMap Y.toRingedSpace n) =
      (boundedAboveFlatPerfectToPerfectKMap X.toRingedSpace n).comp
        (boundedAboveFlatPerfectKPullback f n) :=
  boundedAboveFlatPerfectToPerfectKMap_pullback f n

example (f : X ⟶ Y) [CompactSpace Y] :
    (perfectKPullback f 0).comp (boundedAboveFlatPerfectToPerfectKMap Y.toRingedSpace 0) =
      (boundedAboveFlatPerfectToPerfectKMap X.toRingedSpace 0).comp
        (boundedAboveFlatPerfectKPullback f 0) :=
  boundedAboveFlatPerfectToPerfectKMap_pullback f 0

example (X : Scheme.{u}) [CompactSpace X] (n : ℕ) :
    perfectKPullback (𝟙 X) n = MonoidHom.id ((perfectComplexesWaldhausen X.toRingedSpace).K n) :=
  perfectKPullback_id X n

example (f : X ⟶ Y) (g : Y ⟶ Z) [CompactSpace Y] [CompactSpace Z] (n : ℕ) :
    perfectKPullback (f ≫ g) n = (perfectKPullback f n).comp (perfectKPullback g n) :=
  perfectKPullback_comp f g n

example (f : X ⟶ Y) [CompactSpace Y] (n : ℕ) :
    (perfectKPullback f n).comp (boundedFiniteLocallyFreeToPerfectKMap Y n) =
      (boundedFiniteLocallyFreeToPerfectKMap X n).comp (boundedFiniteLocallyFreeKPullback f n) :=
  boundedFiniteLocallyFreeToPerfectKMap_pullback f n

example (f : X ⟶ Y) [CompactSpace Y] :
    (perfectKPullback f 0).comp (boundedFiniteLocallyFreeToPerfectKMap Y 0) =
      (boundedFiniteLocallyFreeToPerfectKMap X 0).comp (boundedFiniteLocallyFreeKPullback f 0) :=
  boundedFiniteLocallyFreeToPerfectKMap_pullback f 0

example (n : ℕ) : Scheme.{u}ᵒᵖ ⥤ GrpCat.{u + 1} := boundedAboveFlatPerfectKFunctor n

example (n : ℕ) : QuasiCompactSchemes.{u}ᵒᵖ ⥤ GrpCat.{u + 1} := perfectKFunctor n

example (n : ℕ) :
    quasiCompactSchemesInclusion.op ⋙ boundedAboveFlatPerfectKFunctor.{u} n ≅
      perfectKFunctor n := boundedAboveFlatPerfectToPerfectNatIso n

example (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    ((boundedAboveFlatPerfectToPerfectNatIso 0).hom.app X).hom =
      boundedAboveFlatPerfectToPerfectKMap X.unop.obj.toRingedSpace 0 :=
  boundedAboveFlatPerfectToPerfectNatIso_hom_app 0 X

example (n : ℕ) :
    quasiCompactSchemesInclusion.op ⋙ boundedFiniteLocallyFreeKFunctor.{u} n ⟶
      perfectKFunctor n := boundedFiniteLocallyFreeToPerfectNatTrans n
