/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.BaseOpenCover
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.SupportedOpenComparison
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenMaps

/-! # Restriction of projective-line summands to a base open

The first comparison uses the equality of the two projection composites; the second also uses
the canonical pullback isomorphism for the negative line.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage (twistOverPullbackIso)

namespace AlgebraicGeometry.Scheme

universe u

variable {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens)

local notation "J" => projectiveSpaceOverMap 1 j
local notation "P" => projectiveSpaceOver 1 X
local notation "Q" => projectiveSpaceOver 1 V
local notation "Tₚ" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom (P ↘ X))))) T
local notation "U" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom j)))) T
local notation "Uₚ" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom (Q ↘ V))))) U

/-- The untwisted pullbacks agree before retaining the support predicate. -/
def projectiveLineFirstSummand_baseOpenRestrictIso :
    projectiveLineFirstSummand X ⋙ perfectComplexesRestrictOpenImmersion J ≅
      perfectComplexesRestrictOpenImmersion j ⋙ projectiveLineFirstSummand V := by
  let p := (P ↘ X)
  let q := (Q ↘ V)
  let : Flat (J ≫ p) := inferInstance
  let : Flat (q ≫ j) := inferInstance
  let h : J ≫ p = q ≫ j := projectiveSpaceOverMap_fst 1 j
  exact Functor.isoWhiskerLeft _ (perfectRestrictIsoFlatPullback J) ≪≫
    perfectFlatPullbackComp J p ≪≫
    perfectFlatPullbackCongr h ≪≫
    (perfectFlatPullbackComp q j).symm ≪≫
    Functor.isoWhiskerRight (perfectRestrictIsoFlatPullback j).symm _

local notation "L" => twistOver 1 X (-1)
local notation "M" => twistOver 1 V (-1)

local instance baseCoverAmbientTwistFiniteLocallyFree :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
  let : SheafOfModules.IsFiniteLocallyFreeOfRank (R := (P).ringCatSheaf) L 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme P L
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1

local instance baseCoverLocalTwistFiniteLocallyFree :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
  let : SheafOfModules.IsFiniteLocallyFreeOfRank (R := (Q).ringCatSheaf) M 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme Q M
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M 1

/-- The negative line commutes with the actual base-open restriction. -/
def projectiveLineTwist_baseOpenRestrictIso :
    perfectTensorLeft L ⋙ perfectComplexesRestrictOpenImmersion J ≅
      perfectComplexesRestrictOpenImmersion J ⋙ perfectTensorLeft M :=
  perfectOpenRestrictIso_of_complexIso J J
    (Functor.isoWhiskerLeft _ (tensorLeftOpenRestrictionCochainIso J L M
      (twistOverPullbackIso 1 j (-1))))

/-- The twisted pullbacks agree before retaining the support predicate. -/
def projectiveLineSecondSummand_baseOpenRestrictIso :
    projectiveLineSecondSummand X ⋙ perfectComplexesRestrictOpenImmersion J ≅
      perfectComplexesRestrictOpenImmersion j ⋙ projectiveLineSecondSummand V :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (projectiveLineTwist_baseOpenRestrictIso j) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (projectiveLineFirstSummand_baseOpenRestrictIso j) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.Scheme
