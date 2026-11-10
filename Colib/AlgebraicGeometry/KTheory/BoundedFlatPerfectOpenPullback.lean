/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPairPullback
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPullback

/-!
# Actual relative-open bounded-flat K-pullback

Arbitrary commuting open squares act on the original bounded-flat complexes with
open-detected weak equivalences. No support, flatness, compactness or cartesian-square
premise is imposed. The induced K-map uses the actual geometric pullback.

Adapted from Quillen `BoundedFlat/PairPullback.lean:69-80,90-92,111-125,135-140,156-163`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open AlgebraicGeometry.RingedSpace

universe u
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable {A B C : Scheme.OpenPairs.{u}}

/-- Actual pair pullback is exact for the original open-detected weak classes. -/
@[colib_tag "COL-0508",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/PairPullback.lean:69-80"
    "adaptation" "Actual arbitrary-square pullback for the original restricted weak class"]
theorem boundedAboveFlatPerfectOpenPullback_isExact (f : A ⟶ B) :
    IsExact (boundedAboveFlatPerfectOpenWaldhausen B.hom).cof
      (boundedAboveFlatPerfectOpenWaldhausen B.hom).weq
      (boundedAboveFlatPerfectOpenWaldhausen A.hom).cof
      (boundedAboveFlatPerfectOpenWaldhausen A.hom).weq
      (boundedAboveFlatPerfectPullback f.right) where
  zero := (boundedAboveFlatPerfectPullback_isExact f.right).zero
  cofibration := (boundedAboveFlatPerfectPullback_isExact f.right).cofibration
  pushout := (boundedAboveFlatPerfectPullback_isExact f.right).pushout
  weak {K L} p hp :=
    @boundedAboveFlatPerfect_pairPullback_quasiIso A B f K.obj L.obj
      K.property L.property p.hom hp

/-- The canonical K-map of the actual relative geometric pullback. -/
def boundedAboveFlatPerfectOpenKPullback (f : A ⟶ B) (n : ℕ) :
    BoundedAboveFlatPerfectOpenK B.hom n →* BoundedAboveFlatPerfectOpenK A.hom n :=
  KMap (boundedAboveFlatPerfectOpenPullback_isExact f) n

@[simp]
theorem boundedAboveFlatPerfectOpenKPullback_id (A : Scheme.OpenPairs.{u}) (n : ℕ) :
    boundedAboveFlatPerfectOpenKPullback (𝟙 A) n = MonoidHom.id _ :=
  (KMap_eq_of_iso (boundedAboveFlatPerfectOpenPullback_isExact (𝟙 A))
    (IsExact.id (boundedAboveFlatPerfectOpenWaldhausen A.hom).cof
      (boundedAboveFlatPerfectOpenWaldhausen A.hom).weq)
    (boundedAboveFlatPerfectPullbackIdIso A.right) n).trans (KMap_id _ n)

@[simp]
theorem boundedAboveFlatPerfectOpenKPullback_comp (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    boundedAboveFlatPerfectOpenKPullback (f ≫ g) n =
      (boundedAboveFlatPerfectOpenKPullback f n).comp
        (boundedAboveFlatPerfectOpenKPullback g n) :=
  (KMap_eq_of_iso (boundedAboveFlatPerfectOpenPullback_isExact (f ≫ g))
    ((boundedAboveFlatPerfectOpenPullback_isExact g).comp
      (boundedAboveFlatPerfectOpenPullback_isExact f))
    (boundedAboveFlatPerfectPullbackCompIso f.right g.right) n).trans
      (KMap_comp_KMap _ _ n).symm

/-- The original change-of-weak map commutes with actual pair pullback. -/
theorem boundedAboveFlatPerfectOpenKMap_pullback (f : A ⟶ B) (n : ℕ) :
    (boundedAboveFlatPerfectOpenKPullback f n).comp
        (boundedAboveFlatPerfectOpenKMap B.hom n) =
      (boundedAboveFlatPerfectOpenKMap A.hom n).comp
        (boundedAboveFlatPerfectKPullback f.right n) :=
  (KMap_comp_KMap (changeWeak_exact (boundedAboveFlatPerfectOpenNested B.hom))
    (boundedAboveFlatPerfectOpenPullback_isExact f) n).trans
    (KMap_comp_KMap (boundedAboveFlatPerfectPullback_isExact f.right)
      (changeWeak_exact (boundedAboveFlatPerfectOpenNested A.hom)) n).symm

/-- Relative bounded-flat K-theory is contravariant on the native category of open pairs. -/
@[colib_tag "COL-0508",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/PairPullback.lean:156-163"
    "adaptation" "Original relative-open contravariant K-functor with actual geometric maps"]
def BoundedAboveFlatPerfectOpenKFunctor (n : ℕ) : Scheme.OpenPairs.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (BoundedAboveFlatPerfectOpenK X.unop.hom n)
  map f := GrpCat.ofHom (boundedAboveFlatPerfectOpenKPullback f.unop n)
  map_id X := by
    apply GrpCat.hom_ext
    exact boundedAboveFlatPerfectOpenKPullback_id X.unop n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact boundedAboveFlatPerfectOpenKPullback_comp g.unop f.unop n

end AlgebraicGeometry.Scheme.Modules
