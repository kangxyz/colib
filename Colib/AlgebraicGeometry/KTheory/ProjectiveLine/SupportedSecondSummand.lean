/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.SupportedFirstSummand
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.SupportedTwist
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenSupport
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import Colib.Util.References

/-! # The negative twist summand with support -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) (U : X.Opens)

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "V" => Functor.obj
  (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
    (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom π)))) U
local notation "j" => Scheme.Opens.ι V
local notation "L" => twistOver 1 X (-1)
local notation "M" => Functor.obj (pullback j) L

local instance supportedAmbientTwistFiniteLocallyFree :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
  let : SheafOfModules.IsFiniteLocallyFreeOfRank (R := (P).ringCatSheaf) L 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme P L
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1

local instance supportedOpenTwistFiniteLocallyFree :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
  let : Stacks.SheafOfModules.IsInvertible (Scheme.Opens.toScheme V).presheaf
      (Scheme.Opens.toScheme V).ringCatSheaf.2 M := Stacks.Modules.isInvertible_pullback j L
  let : SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := (Scheme.Opens.toScheme V).ringCatSheaf) M 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme
      (Scheme.Opens.toScheme V) M
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M 1

/-- The supported second summand is the actual flat pullback tensored with `𝒪(-1)`. -/
def projectiveLineSupportedSecondSummand :
    (perfectSupported U.ι).FullSubcategory ⥤ (perfectSupported j).FullSubcategory :=
  projectiveLineSupportedFirstSummand X U ⋙ perfectSupportedTensorLeft j L M (Iso.refl M)

/-- The second summand is exact on the supported native full subcategories. -/
theorem projectiveLineSupportedSecondSummand_exact :
    IsExact (perfectSupportedWaldhausen U.ι).cof (perfectSupportedWaldhausen U.ι).weq
      (perfectSupportedWaldhausen j).cof (perfectSupportedWaldhausen j).weq
      (projectiveLineSupportedSecondSummand X U) :=
  (projectiveLineSupportedFirstSummand_exact X U).comp
    (perfectSupportedTensorLeft_exact j L M (Iso.refl M))

local notation "Y" => Scheme.Opens.toScheme V
local notation:max "W[" Z "]" =>
  RingedSpace.perfectComplexesWaldhausen
    (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Z))
local notation:max "R[" f "]" => perfectComplexesRestrictOpenImmersion f
local notation "A" => projectiveLineFirstSummand X
local notation "A'" => projectiveLineOpenFirstSummand X U
local notation "B" => perfectTensorLeft L
local notation "B'" => perfectTensorLeft M

/-- The literal open negative-line summand is the restricted projection followed by the
pulled-back negative line. -/
def projectiveLineOpenSecondSummand := A' ⋙ B'

/-- The actual open negative-line summand is Waldhausen exact. -/
theorem projectiveLineOpenSecondSummand_exact :
    IsExact (W[U.toScheme]).cof (W[U.toScheme]).weq (W[Y]).cof (W[Y]).weq
      (projectiveLineOpenSecondSummand X U) :=
  (projectiveLineOpenFirstSummand_exact X U).comp (perfectTensorLeft_waldhausenExact M)

/-- The negative tensor functor on ordinary perfect complexes commutes with actual restriction. -/
def projectiveLineTwist_restrictIso : B ⋙ R[j] ≅ R[j] ⋙ B' :=
  perfectOpenRestrictIso_of_complexIso j j
    (Functor.isoWhiskerLeft _ (tensorLeftOpenRestrictionCochainIso j L M (Iso.refl M)))

/-- The twisted summand commutes with the actual restriction to the inverse-image open. -/
def projectiveLineSecondSummand_restrictIso :
    projectiveLineSecondSummand X ⋙ R[j] ≅ R[U.ι] ⋙ projectiveLineOpenSecondSummand X U :=
  Functor.associator A B R[j] ≪≫
    Functor.isoWhiskerLeft A (projectiveLineTwist_restrictIso X U) ≪≫
    (Functor.associator A R[j] B').symm ≪≫
    Functor.isoWhiskerRight (projectiveLineFirstSummand_restrictIso X U) B' ≪≫
    Functor.associator R[U.ι] A' B'

/-- The twisted summand is coarse exact for the actual open restriction weak classes. -/
theorem projectiveLineSecondSummand_coarseExact :
    IsExact (perfectOpenWeakWaldhausen U.ι).cof (perfectOpenWeakWaldhausen U.ι).weq
      (perfectOpenWeakWaldhausen j).cof (perfectOpenWeakWaldhausen j).weq
      (projectiveLineSecondSummand X) :=
  perfectOpen_coarseExact_of_restrictIso U.ι j (projectiveLineSecondSummand_exact X)
    (projectiveLineOpenSecondSummand_exact X U) (projectiveLineSecondSummand_restrictIso X U)

/-- The supported twisted summand intertwines the canonical relative boundaries. -/
theorem projectiveLineSupportedSecondSummand_connecting (n : ℕ) :
    (KMap (projectiveLineSupportedSecondSummand_exact X U) n).comp
      (perfectOpenConnectingHom U.ι n) =
    (perfectOpenConnectingHom j n).comp
      (KMap (projectiveLineSecondSummand_coarseExact X U) (n + 1)) :=
  perfectOpenConnectingHom_natural U.ι j (projectiveLineSecondSummand_exact X)
    (projectiveLineSecondSummand_coarseExact X U) (projectiveLineSupportedSecondSummand_exact X U)
    n (Iso.refl _)

/-- The two genuine supported summands define the projective-line map. -/
def projectiveLineSupportedKMap (n : ℕ) :
    PerfectSupportedK U.ι n × PerfectSupportedK U.ι n →* PerfectSupportedK j n := by
  let : CommGroup (PerfectSupportedK j n) := Additivity.KCommGroup (perfectSupportedWaldhausen j) n
  exact (mulMonoidHom : PerfectSupportedK j n × PerfectSupportedK j n →*
    PerfectSupportedK j n).comp
    ((KMap (projectiveLineSupportedFirstSummand_exact X U) n).prodMap
      (KMap (projectiveLineSupportedSecondSummand_exact X U) n))

/-- The supported map commutes with forgetting support on both summands. -/
@[colib_tag "COL-1292"]
theorem projectiveLineSupportedKMap_forget (n : ℕ) :
    (perfectSupportedKMap j n).comp (projectiveLineSupportedKMap X U n) =
      (projectiveLineKMap X n).comp ((perfectSupportedKMap U.ι n).prodMap
        (perfectSupportedKMap U.ι n)) := by
  have h₁ := (KMap_comp_KMap (projectiveLineSupportedFirstSummand_exact X U)
      (perfectSupportedInclusion_isExact j) n).trans
    (KMap_comp_KMap (perfectSupportedInclusion_isExact U.ι)
      (projectiveLineFirstSummand_exact X) n).symm
  have h₂ := (KMap_comp_KMap (projectiveLineSupportedSecondSummand_exact X U)
      (perfectSupportedInclusion_isExact j) n).trans
    (KMap_comp_KMap (perfectSupportedInclusion_isExact U.ι)
      (projectiveLineSecondSummand_exact X) n).symm
  refine MonoidHom.ext fun a => ?_
  change perfectSupportedKMap j n
    (KMap (projectiveLineSupportedFirstSummand_exact X U) n a.1 *
      KMap (projectiveLineSupportedSecondSummand_exact X U) n a.2) =
    projectiveLineKMap X n (perfectSupportedKMap U.ι n a.1, perfectSupportedKMap U.ι n a.2)
  rw [map_mul, projectiveLineKMap_apply]
  exact congrArg₂ (· * ·) (DFunLike.congr_fun h₁ a.1) (DFunLike.congr_fun h₂ a.2)

end AlgebraicGeometry.Scheme
