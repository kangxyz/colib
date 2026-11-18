/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Zariski.Cohomology
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Zariski.Cohomology.Opens.LocalZero
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Zariski.Cohomology.Restriction
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # Cohomology on the ordinary Zariski opens of a smooth scheme -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.FreeYonedaUnivLE

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

attribute [local instance] hasSheafify_zariskiOpens

/-- Ordinary abelian sheaves on the opens of a space have Ext in the coefficient universe. -/
theorem hasExt_zariskiOpens (Y : TopCat.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u + 1}) := by
  let : EssentiallySmall.{u + 1} (Opens Y) :=
    EssentiallySmall.mk' (AsSmall.equiv.{u, u, u + 1} : Opens Y ≌ AsSmall.{u + 1} (Opens Y))
  let : IsGrothendieckAbelian.{u + 1}
      (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall (Opens.grothendieckTopology Y) AddCommGrpCat
  infer_instance

attribute [local instance] hasExt_zariskiOpens

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "Zar" => SmoothSite.zariskiTopology S
set_option hygiene false in
set_option quotPrecheck false in
local notation "Ab" => AddCommGrpCat.{u + 1}

variable (X : SmoothSite (Spec (CommRingCat.of k)))

local notation "J" => _root_.Opens.grothendieckTopology X.left.carrier
local notation "G" => SmoothSite.opensFunctor X
local notation "R" => SmoothSite.restrictZariskiToOpens X Ab

local instance cohomologySmoothZariskiSheafify : HasSheafify Zar Ab :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1} Zar

set_option Elab.async false in
/-- Apply the exact restriction comparison to an ordinary Zariski coefficient. -/
private def zariskiRestrictionCohomologyIso (E : Sheaf Zar Ab) (n : ℕ) :
    (G).op ⋙ cohomologyPresheaf.{u + 1, u + 1} E n ≅
      cohomologyPresheaf.{u + 1, u + 1} ((R).obj E) n := by
  let : PreservesFiniteColimits (R) := SmoothSite.preservesFiniteColimits_restrictZariskiToOpens X
  let : (R).PreservesInjectiveObjects := SmoothSite.preservesInjectives_restrictZariskiToOpens X
  let : (R).IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (G) Ab J Zar).isRightAdjoint
  let : PreservesFiniteLimits (R) := inferInstance
  exact (cohomologyPresheafFunctorRestrictionIso.{u + 1, u + 1} J Zar (G) n).app E

/-- Compose exact restriction with a given comparison of ordinary cohomology presheaves. -/
private def cohomologyOnOpensOfIso (E : Sheaf Zar Ab) (n : ℕ)
    {Q : (SmoothSite S)ᵒᵖ ⥤ Ab} (e : cohomologyPresheaf.{u + 1, u + 1} E n ≅ Q) :
    cohomologyPresheaf.{u + 1, u + 1} ((R).obj E) n ≅ (G).op ⋙ Q :=
  (zariskiRestrictionCohomologyIso k X E n).symm ≪≫ Functor.isoWhiskerLeft (G).op e

variable [PerfectField k] (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)

local notation "FN" => Functor.obj (toSheaf k) F
local notation "FZ" => Functor.obj (SmoothSite.nisnevichToZariskiSheaf S Ab) (FN)

include hF in
private def zariskiNisnevichCohomologyIso (n : ℕ) :
    cohomologyPresheaf.{u + 1, u + 1} (FZ) n ≅ cohomologyPresheaf.{u + 1, u + 1} (FN) n := by
  let : IsIso (zariskiCohomologyComparison k F n) := isIso_zariskiCohomologyComparison k F hF n
  exact asIso (zariskiCohomologyComparison k F n)

set_option maxHeartbeats 450000 in
-- The final specialization compares the actual coefficient sheaf representations.
include hF in
/-- Ordinary cohomology on Zariski opens agrees with the original ordinary
Nisnevich cohomology presheaf restricted to those opens. -/
@[no_expose, colib_tag "COL-1307"]
def zariskiCohomologyOnOpensIso (n : ℕ) :
    cohomologyPresheaf.{u + 1, u + 1} (zariskiSheafOnOpens k X F) n ≅
      (G).op ⋙ cohomologyPresheaf.{u + 1, u + 1} (FN) n :=
  cohomologyOnOpensOfIso k X (FZ) n (zariskiNisnevichCohomologyIso k F hF n)

end AlgebraicGeometry.SheafWithTransfers
