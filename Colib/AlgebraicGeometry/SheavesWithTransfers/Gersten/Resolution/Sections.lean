/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Gersten.Resolution
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Zariski.Cohomology.Opens

/-! # Ordinary Zariski cohomology of sections of the Cousin resolution -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme Opposite TopologicalSpace
open Stacks.Cohomology.FreeYonedaUnivLE

universe u w

namespace AlgebraicGeometry.Gersten

open MotivicHomotopy SheafWithTransfers

attribute [local instance] hasSheafify_zariskiOpens hasExt_zariskiOpens

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{u + 1} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (X : SmoothSite (Spec (CommRingCat.of k)))
  (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)

set_option hygiene false in
set_option quotPrecheck false in
local notation "Ab" => AddCommGrpCat.{u + 1}
local notation "J" => _root_.Opens.grothendieckTopology X.left.carrier
local notation "K" => effectiveHICoefficient k F hF

/-- Use the transfer-sheaf abelian structure in the cohomology comparison on sections. -/
local instance cousinSectionsAbelian : Abelian (LargeSheaves k) := SheafWithTransfers.abelian k

/-- Sections of the Cousin complex compute positive ordinary Zariski
cohomology when the windows are concentrated on the diagonal and their
diagonal presheaves already satisfy descent. -/
@[no_expose]
def zariskiCousinSectionsCohomologySuccIso
    (h : ∀ (U : X.left.Opens) (p n : ℕ), p ≠ n →
      IsZero (coniveauRelativeSupportCohomology k ((SmoothSite.opensFunctor X).obj U)
        K (n : ℤ) p (p + 1)))
    (hSheaf : ∀ p : ℕ, Presheaf.IsSheaf J (coniveauWindowPresheaf k X K p (p : ℤ)))
    (U : X.left.Opens) (n : ℕ) :
    (((sheafToPresheaf J Ab ⋙ (CategoryTheory.evaluation _ _).obj (op U)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (zariskiCousinComplex k X F hF h)).homology (n + 1) ≅
      (cohomologyPresheaf.{u + 1, u + 1} (zariskiSheafOnOpens k X F) (n + 1)).obj (op U) := by
  let e := zariskiCousinSectionsHomologySuccIso k X F hF h hSheaf U n
  let c := zariskiCohomologyOnOpensIso k X F hF (n + 1)
  exact e ≪≫ c.symm.app (op U)

end AlgebraicGeometry.Gersten
