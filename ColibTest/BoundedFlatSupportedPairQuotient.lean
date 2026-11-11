/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPairPullback

/-! Arbitrary nonflat pair pullback retains the same complex, map and admissible quotient. -/
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace

universe u
attribute [local instance] Abelian.hasFiniteBiproducts

variable {A B : Scheme.OpenPairs.{u}} (f : A ⟶ B)

example (K : (boundedAboveFlatPerfectSupported B.hom).FullSubcategory) :
    ((boundedAboveFlatPerfectSupportedPullback f).obj K).obj =
      (((Scheme.Modules.pullback f.right).mapHomologicalComplex (.up ℤ)).obj K.obj) := rfl

example {K L : (boundedAboveFlatPerfectSupported B.hom).FullSubcategory} (p : K ⟶ L) :
    ((boundedAboveFlatPerfectSupportedPullback f).map p).hom =
      (((Scheme.Modules.pullback f.right).mapHomologicalComplex (.up ℤ)).map p.hom) := rfl

example (S : ShortComplex (boundedAboveFlatPerfectSupported B.hom).FullSubcategory)
    (hS : (S.map (boundedAboveFlatPerfectSupported B.hom).ι).ShortExact) :
    ((S.map (boundedAboveFlatPerfectSupportedPullback f)).map
      (boundedAboveFlatPerfectSupported A.hom).ι).ShortExact :=
  (boundedAboveFlatPerfectSupportedExactPullback f).map_conflation S hS

example (S : ShortComplex (boundedAboveFlatPerfectSupported B.hom).FullSubcategory) :
    ((S.map (boundedAboveFlatPerfectSupportedPullback f)).X₃).obj =
      (((Scheme.Modules.pullback f.right).mapHomologicalComplex (.up ℤ)).obj S.X₃.obj) := rfl

example {K L : CochainComplex B.right.Modules ℤ}
    (hK : boundedAboveFlatPerfectComplex B.right.toRingedSpace K)
    (hL : boundedAboveFlatPerfectComplex B.right.toRingedSpace L) (p : K ⟶ L)
    [QuasiIso (((restrictFunctor B.hom).mapHomologicalComplex (.up ℤ)).map p)] :
    QuasiIso (((restrictFunctor A.hom).mapHomologicalComplex (.up ℤ)).map
      (((Scheme.Modules.pullback f.right).mapHomologicalComplex (.up ℤ)).map p)) :=
  boundedAboveFlatPerfect_pairPullback_quasiIso f hK hL p

example :
    (Scheme.Modules.pullback f.right).mapHomologicalComplex (.up ℤ) ⋙
        (restrictFunctor A.hom).mapHomologicalComplex (.up ℤ) ≅
      (restrictFunctor B.hom).mapHomologicalComplex (.up ℤ) ⋙
        (Scheme.Modules.pullback f.left).mapHomologicalComplex (.up ℤ) :=
  pullbackComplexOpenPairIso f
