/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Gersten.Basic
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Gersten.Resolution.Sections

/-! # Computing ordinary Zariski cohomology with the Gersten complex -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme Opposite TopologicalSpace
open Stacks.Cohomology.FreeYonedaUnivLE

universe u w

namespace AlgebraicGeometry.SheafWithTransfers.Gersten

open AlgebraicGeometry.Gersten MotivicHomotopy

attribute [local instance] hasSheafify_zariskiOpens hasExt_zariskiOpens

variable (k : Type u) [Field k] [PerfectField k]

attribute [local instance] effectiveSupportCoefficientCorSheafify
  effectiveSupportCoefficientSmoothSheafify

/-- Use the original transfer coefficient category when computing Zariski cohomology. -/
local instance gerstenSectionsAbelian : Abelian (LargeSheaves k) := SheafWithTransfers.abelian k

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{u + 1} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{u + 1} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

set_option hygiene false in
set_option quotPrecheck false in
local notation "Ab" => AddCommGrpCat.{u + 1}

variable (X : SmoothSite (Spec (CommRingCat.of k)))
  (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)

local notation "K" => effectiveHICoefficient k F hF
local notation "J" => _root_.Opens.grothendieckTopology X.left.carrier

/-- Sections of the Gersten resolution over an open compute the ordinary
Zariski cohomology groups in positive degrees. -/
@[colib_tag "COL-1310", no_expose]
def gerstenSectionsCohomologySuccIso (U : X.left.Opens) (n : ℕ) :
    (((sheafToPresheaf J Ab ⋙ (CategoryTheory.evaluation _ _).obj (op U)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (gerstenComplex k X F hF)).homology (n + 1) ≅
      (cohomologyPresheaf.{u + 1, u + 1} (zariskiSheafOnOpens k X F) (n + 1)).obj (op U) := by
  have hSheaf (p : ℕ) : Presheaf.IsSheaf J (coniveauWindowPresheaf k X K p (p : ℤ)) :=
    (Presheaf.isSheaf_of_iso_iff (coniveauWindowCousinPresheafIso k X K p (p : ℤ))).1
      (coniveauCousinPointSheaf k X K p (p : ℤ)).property
  let h := fun W p d hp ↦
    isZero_coniveauWindow_of_ne k F hF ((SmoothSite.opensFunctor X).obj W) p d hp
  exact zariskiCousinSectionsCohomologySuccIso k X F hF h hSheaf U n

end AlgebraicGeometry.SheafWithTransfers.Gersten
