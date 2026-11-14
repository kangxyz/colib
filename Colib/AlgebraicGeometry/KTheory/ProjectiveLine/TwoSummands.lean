/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectFlatPullback
public import Colib.AlgebraicGeometry.KTheory.PerfectVectorBundleTensor
public import Colib.KTheory.Waldhausen.Additivity.GroupFormula
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic

/-! # The two summands of the projective-line formula

For the standard projective line over a scheme, flat pullback and its tensor product with
`𝒪(-1)` give two exact functors on the native categories of perfect complexes. The direct sum
of these functors induces the projective bundle map on connective K-groups.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Perf₀" => ObjectProperty.FullSubcategory (IsPerfectComplex (X := X.toRingedSpace))
local notation "Perf₁" =>
  ObjectProperty.FullSubcategory
    (IsPerfectComplex (X := LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace P)))
local notation "W" Y =>
  perfectComplexesWaldhausen (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y))

local instance : SheafOfModules.IsFiniteLocallyFree (R := (P).ringCatSheaf) (twistOver 1 X (-1)) :=
  let : SheafOfModules.IsFiniteLocallyFreeOfRank (R := (P).ringCatSheaf) (twistOver 1 X (-1)) 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme P _
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

local instance : HasBinaryCoproducts Perf₁ :=
  Additivity.hasBinaryCoproducts (W P)

/-- The structure-line summand is actual flat pullback. -/
def projectiveLineFirstSummand : Perf₀ ⥤ Perf₁ :=
  perfectFlatPullback π

/-- The negative-line summand is flat pullback followed by tensoring with `𝒪(-1)`. -/
def projectiveLineSecondSummand : Perf₀ ⥤ Perf₁ :=
  projectiveLineFirstSummand X ⋙ perfectTensorLeft (twistOver 1 X (-1))

theorem projectiveLineFirstSummand_exact :
    IsExact (W X).cof (W X).weq (W P).cof (W P).weq (projectiveLineFirstSummand X) :=
  perfectFlatPullback_waldhausenExact π

theorem projectiveLineSecondSummand_exact :
    IsExact (W X).cof (W X).weq (W P).cof (W P).weq (projectiveLineSecondSummand X) :=
  (projectiveLineFirstSummand_exact X).comp
    (perfectTensorLeft_waldhausenExact (twistOver 1 X (-1)))

/-- The projective-line functor `(E,F) ↦ π*E ⊕ (𝒪(-1) ⊗ π*F)`. -/
def projectiveLineTwoSummands : Perf₀ × Perf₀ ⥤ Perf₁ :=
  CategoryTheory.sumFunctor
    (CategoryTheory.Prod.fst _ _ ⋙ projectiveLineFirstSummand X)
    (CategoryTheory.Prod.snd _ _ ⋙ projectiveLineSecondSummand X)

theorem projectiveLineTwoSummands_exact :
    IsExact (Product.productStructure (W X) (W X)).cof (Product.productStructure (W X) (W X)).weq
      (W P).cof (W P).weq (projectiveLineTwoSummands X) :=
  Additivity.sumFunctor_isExact _ _
    ((Product.fst_exact _ _).comp (projectiveLineFirstSummand_exact X))
    ((Product.snd_exact _ _).comp (projectiveLineSecondSummand_exact X))

/-- The projective-line map on connective K-groups. -/
def projectiveLineKMap (n : ℕ) : (W X).K n × (W X).K n →* (W P).K n :=
  (KMap (projectiveLineTwoSummands_exact X) n).comp
    (Product.KEquiv (W X) (W X) n).symm.toMonoidHom

/-- The two components of the projective-line map are the actual summand K-maps. -/
theorem projectiveLineKMap_apply (n : ℕ) (a b : (W X).K n) :
    projectiveLineKMap X n (a, b) =
      KMap (projectiveLineFirstSummand_exact X) n a *
        KMap (projectiveLineSecondSummand_exact X) n b := by
  let z := (Product.KEquiv (W X) (W X) n).symm (a, b)
  have hz :
      (KMap (Product.fst_exact (W X) (W X)) n z,
        KMap (Product.snd_exact (W X) (W X)) n z) = (a, b) :=
    (Product.KEquiv (W X) (W X) n).apply_symm_apply _
  change KMap (projectiveLineTwoSummands_exact X) n z = _
  have hsum :
      KMap (projectiveLineTwoSummands_exact X) n z =
        KMap ((Product.fst_exact (W X) (W X)).comp (projectiveLineFirstSummand_exact X)) n z *
          KMap ((Product.snd_exact (W X) (W X)).comp (projectiveLineSecondSummand_exact X)) n z :=
    Additivity.KMap_sum_apply (Product.productStructure (W X) (W X)) (W P)
      ((Product.fst_exact (W X) (W X)).comp (projectiveLineFirstSummand_exact X))
      ((Product.snd_exact (W X) (W X)).comp (projectiveLineSecondSummand_exact X)) n z
  rw [hsum]
  rw [← KMap_comp_KMap (Product.fst_exact (W X) (W X)) (projectiveLineFirstSummand_exact X),
    ← KMap_comp_KMap (Product.snd_exact (W X) (W X)) (projectiveLineSecondSummand_exact X)]
  change KMap (projectiveLineFirstSummand_exact X) n _ *
      KMap (projectiveLineSecondSummand_exact X) n _ = _
  exact congrArg₂ (fun x y => KMap (projectiveLineFirstSummand_exact X) n x *
    KMap (projectiveLineSecondSummand_exact X) n y)
    (congrArg _root_.Prod.fst hz) (congrArg _root_.Prod.snd hz)

end AlgebraicGeometry.Scheme

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/NativeTwoSummands.lean:145-186"
  "adaptation" "The two-summand functor and K-map on the standard Stacks projective line"]
  AlgebraicGeometry.Scheme.projectiveLineTwoSummands
  AlgebraicGeometry.Scheme.projectiveLineTwoSummands_exact
  AlgebraicGeometry.Scheme.projectiveLineKMap
  AlgebraicGeometry.Scheme.projectiveLineKMap_apply
