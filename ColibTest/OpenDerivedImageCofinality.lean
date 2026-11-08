/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.OpenDerivedImageCofinality

/-! The original maps, genuine coproducts, arbitrary derived model and exact K-zero image
are retained. Only actual geometric roofs and actual-complex complements are inputs. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{d} U.Modules]

example : HasBinaryCoproducts
    (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := U.toRingedSpace))) :=
  inferInstance

example (hroof : HasDerivedRoofs j) (hc : HasPerfectComplements j) :
    Cofinality.DenseCofiberData (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)
      (objects j) := denseCofiberData j hroof hc

example (hc : ∀ (P : CochainComplex U.Modules ℤ),
    RingedSpace.IsPerfectComplex (X := U.toRingedSpace) P →
    ∃ (R : CochainComplex X.Modules ℤ) (C : CochainComplex U.Modules ℤ),
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) R ∧
      RingedSpace.IsPerfectComplex (X := U.toRingedSpace) C ∧
      Nonempty (DerivedCategory.Q.obj
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj R) ≅
        DerivedCategory.Q.obj (P ⊞ C))) : HasPerfectComplements j := hc

example : flatten j ⋙ inclusion j = (objects j).ι := rfl

example [Fact (HasDerivedRoofs j)] (hc : HasPerfectComplements j) (n : ℕ) :
    Function.Injective (KMap (inclusion_isExact j Fact.out) n) :=
  inclusion_KMap_injective j hc n

example [Fact (HasDerivedRoofs j)] (hc : HasPerfectComplements j) (n : ℕ) :
    Function.Bijective (KMap (inclusion_isExact j Fact.out) (n + 1)) :=
  inclusion_KMap_succ_bijective j hc n

example [Fact (HasDerivedRoofs j)] (hc : HasPerfectComplements j) (n : ℕ) :
    Function.Injective (perfectOpenKRestrict j n) := relativeKRestrict_injective j hc n

example [Fact (HasDerivedRoofs j)] (hc : HasPerfectComplements j) (n : ℕ) :
    Function.Bijective (perfectOpenKRestrict j (n + 1)) :=
  relativeKRestrict_succ_bijective j hc n

example [Fact (HasDerivedRoofs j)] (hc : HasPerfectComplements j) :
    (relativeKRestrictEquiv j hc 0).toMonoidHom = perfectOpenKRestrict j 1 := rfl

example [Fact (HasDerivedRoofs j)] (hc : HasPerfectComplements j) :
    (relativeKZeroImageEquiv j hc).toMonoidHom = perfectOpenKZeroToImage j := rfl

example [Fact (HasDerivedRoofs j)] (hc : HasPerfectComplements j) (x : PerfectOpenK j 0) :
    (relativeKZeroImageEquiv j hc x :
      (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K 0) =
        perfectOpenKRestrict j 0 x := rfl

example [Fact (HasDerivedRoofs j)] :
    (KMap (inclusion_isExact j Fact.out) 0).range =
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0).range :=
  range_inclusion_KMap_zero j

example [Fact (HasDerivedRoofs j)] (hc : HasPerfectComplements j) :
    (KMap (denseCofiberData j Fact.out hc).inclusion_exact 0).range =
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0).range :=
  range_dense_inclusion_KMap_zero j hc
