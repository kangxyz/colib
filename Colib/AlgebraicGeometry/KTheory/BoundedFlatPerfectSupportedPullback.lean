/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPairPullback
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPullback

/-!
# Actual supported bounded-flat K-pullback

Arbitrary commuting squares of opens act by the original exact geometric pullback.
The functor retains its actual flat quotient and the canonical K-map in every natural degree.
Neither compactness nor flatness of the ambient morphism is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open AlgebraicGeometry.RingedSpace

universe u
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable {A B C : Scheme.OpenPairs.{u}}

/-- Arbitrary pair pullback is exact for the original supported quotient and weak classes. -/
@[colib_tag "COL-0507",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/PairPullback.lean:45-66"
    "adaptation" "Actual supported pullback with unchanged admissible flat quotient"]
theorem boundedAboveFlatPerfectSupportedPullback_isExact (f : A ⟶ B) :
    IsExact (boundedAboveFlatPerfectSupportedWaldhausen B.hom).cof
      (boundedAboveFlatPerfectSupportedWaldhausen B.hom).weq
      (boundedAboveFlatPerfectSupportedWaldhausen A.hom).cof
      (boundedAboveFlatPerfectSupportedWaldhausen A.hom).weq
      (boundedAboveFlatPerfectSupportedPullback f) where
  zero h := (boundedAboveFlatPerfectSupportedPullback f).map_isZero h
  cofibration p hp := (boundedAboveFlatPerfectSupportedExactPullback f).map_inflation p hp
  weak {K L} p hp := by
    let : QuasiIso p.hom := hp
    exact quasiIso_pullback_of_boundedAboveFlatPerfect f.right K.property.1 L.property.1 p.hom
  pushout hi h := (boundedAboveFlatPerfectSupportedExactPullback f).map_isPushout hi h

/-- The original supported geometric pullback induces its canonical K-map. -/
def boundedAboveFlatPerfectSupportedKPullback (f : A ⟶ B) (n : ℕ) :
    BoundedAboveFlatPerfectSupportedK B.hom n →* BoundedAboveFlatPerfectSupportedK A.hom n :=
  KMap (boundedAboveFlatPerfectSupportedPullback_isExact f) n

@[simp]
theorem boundedAboveFlatPerfectSupportedKPullback_id (A : Scheme.OpenPairs.{u}) (n : ℕ) :
    boundedAboveFlatPerfectSupportedKPullback (𝟙 A) n = MonoidHom.id _ :=
  (KMap_eq_of_iso (boundedAboveFlatPerfectSupportedPullback_isExact (𝟙 A))
    (IsExact.id (boundedAboveFlatPerfectSupportedWaldhausen A.hom).cof
      (boundedAboveFlatPerfectSupportedWaldhausen A.hom).weq)
    (boundedAboveFlatPerfectSupportedPullbackIdIso A) n).trans (KMap_id _ n)

@[simp]
theorem boundedAboveFlatPerfectSupportedKPullback_comp (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    boundedAboveFlatPerfectSupportedKPullback (f ≫ g) n =
      (boundedAboveFlatPerfectSupportedKPullback f n).comp
        (boundedAboveFlatPerfectSupportedKPullback g n) :=
  (KMap_eq_of_iso (boundedAboveFlatPerfectSupportedPullback_isExact (f ≫ g))
    ((boundedAboveFlatPerfectSupportedPullback_isExact g).comp
      (boundedAboveFlatPerfectSupportedPullback_isExact f))
    (boundedAboveFlatPerfectSupportedPullbackCompIso f g) n).trans
      (KMap_comp_KMap (boundedAboveFlatPerfectSupportedPullback_isExact g)
        (boundedAboveFlatPerfectSupportedPullback_isExact f) n).symm

/-- Forgetting support commutes with the original geometric K-pullback. -/
theorem boundedAboveFlatPerfectSupportedForgetKMap_pullback (f : A ⟶ B) (n : ℕ) :
    (boundedAboveFlatPerfectKPullback f.right n).comp
        (boundedAboveFlatPerfectSupportedForgetKMap B.hom n) =
      (boundedAboveFlatPerfectSupportedForgetKMap A.hom n).comp
        (boundedAboveFlatPerfectSupportedKPullback f n) := by
  exact (KMap_comp_KMap (boundedAboveFlatPerfectSupportedForget_isExact B.hom)
    (boundedAboveFlatPerfectPullback_isExact f.right) n).trans
    (KMap_comp_KMap (boundedAboveFlatPerfectSupportedPullback_isExact f)
      (boundedAboveFlatPerfectSupportedForget_isExact A.hom) n).symm

/-- Original supported K-theory is contravariant on the native category of open pairs. -/
@[colib_tag "COL-0507",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/PairPullback.lean:144-153"
    "adaptation" "Contravariant supported K-functor on arbitrary commuting open squares"]
def BoundedAboveFlatPerfectSupportedKFunctor (n : ℕ) : Scheme.OpenPairs.{u}ᵒᵖ ⥤ GrpCat.{u + 1}
    where
  obj X := GrpCat.of (BoundedAboveFlatPerfectSupportedK X.unop.hom n)
  map f := GrpCat.ofHom (boundedAboveFlatPerfectSupportedKPullback f.unop n)
  map_id X := by
    apply GrpCat.hom_ext
    exact boundedAboveFlatPerfectSupportedKPullback_id X.unop n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact boundedAboveFlatPerfectSupportedKPullback_comp g.unop f.unop n

end AlgebraicGeometry.Scheme.Modules
