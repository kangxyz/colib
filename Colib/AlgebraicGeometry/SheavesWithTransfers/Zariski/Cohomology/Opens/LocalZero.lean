/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Zariski.Cohomology.LocalZero
public import Colib.AlgebraicGeometry.Sites.Smooth.Zariski.Opens
import Mathlib.CategoryTheory.Sites.CoverLifting
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # Local vanishing on the ordinary Zariski opens of a smooth scheme -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.FreeYonedaUnivLE

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

/-- Abelian sheafification on ordinary opens in a coefficient universe one
level above that of the space. -/
theorem hasSheafify_zariskiOpens (Y : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u + 1} := by
  let : EssentiallySmall.{u + 1} (Opens Y) :=
    EssentiallySmall.mk' (AsSmall.equiv.{u, u, u + 1} : Opens Y ≌ AsSmall.{u + 1} (Opens Y))
  exact GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1} _

attribute [local instance] hasSheafify_zariskiOpens

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

local instance smallZariskiSmoothSheafify : HasSheafify Zar Ab :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1} Zar

/-- Restrict the ordinary coefficient sheaf to the Zariski opens of a smooth scheme. -/
abbrev zariskiSheafOnOpens (F : SheafWithTransfers.{u + 1} k) : Sheaf J Ab :=
  (R).obj ((SmoothSite.nisnevichToZariskiSheaf S Ab).obj ((toSheaf k).obj F))

variable [PerfectField k] (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)

include hF in
set_option Elab.async false in
-- Use the existing higher-cohomology zero sieve on the smooth Zariski site.
/-- The presheaf of positive Nisnevich cohomology on the actual opens of
`X` has zero associated Zariski sheaf. -/
theorem isZero_zariskiSheafify_nisCohomologyOnOpens_succ (n : ℕ) :
    IsZero ((presheafToSheaf J Ab).obj
      ((G).op ⋙ cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) (n + 1))) := by
  let : PreservesFiniteColimits (R) := SmoothSite.preservesFiniteColimits_restrictZariskiToOpens X
  let : (R).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_initial_object (F := (R))
  let P : (SmoothSite S)ᵒᵖ ⥤ Ab :=
    cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) (n + 1)
  let : (Zar).WEqualsLocallyBijective Ab := SmoothSite.wEqualsLocallyBijective_addCommGrpCat Zar
  have hP : IsZero ((presheafToSheaf Zar Ab).obj P) :=
    Presheaf.isZero_sheafify_of_locally_zero Zar P
      (zeroSieve_mem_zariskiTopology_succ_of_perfect k F hF n)
  let e : (presheafToSheaf J Ab).obj ((G).op ⋙ P) ≅
      (R).obj ((presheafToSheaf Zar Ab).obj P) :=
    ((G).pushforwardContinuousSheafificationCompatibility Ab J Zar).app P
  exact ((R).map_isZero hP).of_iso e

end AlgebraicGeometry.SheafWithTransfers
