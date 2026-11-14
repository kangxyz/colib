/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.SupportedSecondSummand
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.OpenBaseChangeKMap
public import Colib.AlgebraicGeometry.Modules.PerfectFlatPullbackComposition
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.TwistCongr
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Vanishing

/-! # Identifying the actual two summands on the inverse-image open -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) (U : X.Opens)

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Q" => projectiveSpaceOver 1 (Scheme.Opens.toScheme U)
local notation "V" => Functor.obj
  (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
    (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom π)))) U
local notation "Y" => Scheme.Opens.toScheme V
local notation "j" => Scheme.Opens.ι V
local notation "L" => twistOver 1 X (-1)
local notation "e" => projectiveLineOpenBaseChangeIso X U

/-- Pulling the negative line from the projective line over the open to the literal inverse image
is the same as restricting the ambient negative line. -/
def projectiveLineOpenNegativeTwistIso :
    (pullback (e).inv).obj (twistOver 1 U.toScheme (-1)) ≅ (pullback j).obj L := by
  let w : (e).inv ≫ projectiveSpaceOverMap 1 U.ι = j := by
    rw [← projectiveLineOpenBaseChangeIso_hom_ι X U, Iso.inv_hom_id_assoc]
  exact (pullback (e).inv).mapIso (twistOverPullbackIso 1 U.ι (-1)).symm ≪≫
    (pullbackComp (e).inv (projectiveSpaceOverMap 1 U.ι)).app L ≪≫
    (pullbackCongr w).app L

/-- The ordinary first summand followed by the native base-change pullback is the literal
first summand on the inverse-image open. -/
def projectiveLineOpenFirstSummand_comparison :
    projectiveLineFirstSummand U.toScheme ⋙ perfectFlatPullback (e).inv ≅
      projectiveLineOpenFirstSummand X U := by
  let π' := (Q ↘ U.toScheme)
  let : Flat π' := inferInstanceAs (Flat (Q ↘ U.toScheme))
  let : Flat ((π).resLE U (V) le_rfl) := projectiveLineSupportRestriction_flat_left X U
  have h : (e).inv ≫ π' = (π).resLE U (V) le_rfl := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact (congrArg (fun g : Q ⟶ U.toScheme => (e).inv ≫ g)
      (projectiveLineOpenBaseChangeIso_hom_morphismRestrict X U).symm).trans
        (Iso.inv_hom_id_assoc (e) _)
  exact perfectFlatPullbackComp (e).inv π' ≪≫
    perfectFlatPullbackCongr h

local instance openBaseTwistFiniteLocallyFree :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (twistOver 1 U.toScheme (-1)) :=
  let : SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := (Q).ringCatSheaf) (twistOver 1 U.toScheme (-1)) 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme Q _
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

local notation "M" => Functor.obj (pullback j) L

local instance openInverseImageTwistFiniteLocallyFree :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
  let : Stacks.SheafOfModules.IsInvertible (Y).presheaf (Y).ringCatSheaf.2 M :=
    Stacks.Modules.isInvertible_pullback j L
  let : SheafOfModules.IsFiniteLocallyFreeOfRank (R := (Y).ringCatSheaf) M 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme Y M
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M 1

/-- The ordinary second summand followed by base-change pullback is the actual
negative-line summand on the inverse-image open. -/
def projectiveLineOpenSecondSummand_comparison :
    projectiveLineSecondSummand U.toScheme ⋙ perfectFlatPullback (e).inv ≅
      projectiveLineOpenSecondSummand X U :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (projectiveLineFirstSummand U.toScheme)
      (perfectTensorLeft_pullbackIso _ (e).inv M (projectiveLineOpenNegativeTwistIso X U)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (projectiveLineOpenFirstSummand_comparison X U)
      (perfectTensorLeft M)

variable [CompactSpace U.toScheme]

/-- The open map evaluates on the two actual open summands. -/
theorem projectiveLineOpenKMap_apply (n : ℕ)
    (a b : (RingedSpace.perfectComplexesWaldhausen U.toScheme.toRingedSpace).K n) :
    projectiveLineOpenKMap X U n (a, b) =
      KMap (projectiveLineOpenFirstSummand_exact X U) n a *
      KMap (projectiveLineOpenSecondSummand_exact X U) n b := by
  let : IsProper (Q ↘ U.toScheme) := isProper_projectiveSpaceOver 1 U.toScheme
  let : CompactSpace Q := QuasiCompact.compactSpace_of_compactSpace (Q ↘ U.toScheme)
  let h := perfectFlatPullback_waldhausenExact (e).inv
  change perfectKPullback (e).inv n (projectiveLineKMap U.toScheme n (a, b)) = _
  rw [perfectKPullback_eq_flatPullback, projectiveLineKMap_apply, map_mul]
  have h₁ := (KMap_comp_KMap (projectiveLineFirstSummand_exact U.toScheme) h n).trans
    (KMap_eq_of_iso _ (projectiveLineOpenFirstSummand_exact X U)
      (projectiveLineOpenFirstSummand_comparison X U) n)
  have h₂ := (KMap_comp_KMap (projectiveLineSecondSummand_exact U.toScheme) h n).trans
    (KMap_eq_of_iso _ (projectiveLineOpenSecondSummand_exact X U)
      (projectiveLineOpenSecondSummand_comparison X U) n)
  exact congrArg₂ (· * ·) (DFunLike.congr_fun h₁ a) (DFunLike.congr_fun h₂ b)

/-- The ordinary formula and the formula on its inverse-image open commute with restriction. -/
theorem projectiveLineKMap_restrict (n : ℕ) :
    (KMap (perfectComplexesRestrictOpenImmersion_isExact j) n).comp (projectiveLineKMap X n) =
      (projectiveLineOpenKMap X U n).comp
        ((KMap (perfectComplexesRestrictOpenImmersion_isExact U.ι) n).prodMap
          (KMap (perfectComplexesRestrictOpenImmersion_isExact U.ι) n)) := by
  refine MonoidHom.ext fun a => ?_
  change KMap (perfectComplexesRestrictOpenImmersion_isExact j) n
    (projectiveLineKMap X n (a.1, a.2)) =
    projectiveLineOpenKMap X U n
      (KMap (perfectComplexesRestrictOpenImmersion_isExact U.ι) n a.1,
       KMap (perfectComplexesRestrictOpenImmersion_isExact U.ι) n a.2)
  rw [projectiveLineKMap_apply, projectiveLineOpenKMap_apply, map_mul]
  have h₁ := (KMap_comp_KMap (projectiveLineFirstSummand_exact X)
      (perfectComplexesRestrictOpenImmersion_isExact j) n).trans
    ((KMap_eq_of_iso _ _ (projectiveLineFirstSummand_restrictIso X U) n).trans
      (KMap_comp_KMap (perfectComplexesRestrictOpenImmersion_isExact U.ι)
        (projectiveLineOpenFirstSummand_exact X U) n).symm)
  have h₂ := (KMap_comp_KMap (projectiveLineSecondSummand_exact X)
      (perfectComplexesRestrictOpenImmersion_isExact j) n).trans
    ((KMap_eq_of_iso _ _ (projectiveLineSecondSummand_restrictIso X U) n).trans
      (KMap_comp_KMap (perfectComplexesRestrictOpenImmersion_isExact U.ι)
        (projectiveLineOpenSecondSummand_exact X U) n).symm)
  exact congrArg₂ (· * ·) (DFunLike.congr_fun h₁ a.1) (DFunLike.congr_fun h₂ a.2)

end AlgebraicGeometry.Scheme
