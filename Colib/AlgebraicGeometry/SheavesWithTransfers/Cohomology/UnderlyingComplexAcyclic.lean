/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.UnderlyingExactness
public import Colib.AlgebraicGeometry.Sites.Smooth.Injectives
import Colib.AlgebraicGeometry.SheavesWithTransfers.Germs.Envelope.Acyclic
import Colib.AlgebraicGeometry.Sites.Smooth.FiniteKrullDimension
import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteCohomologicalDimension
import StacksFrontier.Algebra.Homology.DerivedCategory.TermwiseAcyclicComputesRightDerived
import StacksFrontier.Algebra.Homology.DerivedCategory.SheafSectionsRightDerived
import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaRightDerivedUnivLE
import Mathlib.Algebra.Homology.Functor

/-!
# Ordinary presheaves underlying complexes of transfer injectives

Each smooth evaluation has finite cohomological dimension, and the
ordinary sheaf underlying a transfer-injective coefficient is acyclic
for that evaluation. Consequently the actual ordinary presheaf complex
underlying a termwise transfer-injective complex computes derived
forget on the ordinary Nisnevich site.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme
open Stacks.Cohomology.FreeYonedaUnivLE
open Stacks.Injectives.KInjectiveResolution

universe u

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "J" => SmoothSite.nisnevichTopology S
local notation "F" => toSheaf k
local notation "U" => sheafToPresheaf J _
local notation "c" => ComplexShape.up ℤ

private abbrev sectionsAt (X : SmoothSite S) :
    Sheaf J AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  (sheafSections J _).obj (op X)

private theorem isZero_rightDerived_sectionsAt_of_krullDim_lt
    [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})] (X : SmoothSite S) (n : ℕ)
    (hn : topologicalKrullDim X.left < n) (N : Sheaf J AddCommGrpCat.{u + 1}) :
    IsZero (((sectionsAt k X).rightDerived n).obj N) := by
  let e := cohomologyPresheafObjIsoRightDerivedSections.{u + 1} J N n X
  refine AddCommGrpCat.isZero_iff_subsingleton.2 ⟨fun a b => ?_⟩
  apply (ConcreteCategory.bijective_of_isIso e.inv).injective
  exact (SmoothSite.nisnevichCohomology_eq_zero_of_krullDim_lt N n X hn (e.inv a)).trans
    (SmoothSite.nisnevichCohomology_eq_zero_of_krullDim_lt N n X hn (e.inv b)).symm

private theorem isZero_rightDerived_sectionsAt_underlying_injective
    [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})] (X : SmoothSite S)
    (P : SheafWithTransfers.{u + 1} k) [Injective P] (n : ℕ) :
    IsZero (((sectionsAt k X).rightDerived (n + 1)).obj ((F).obj P)) := by
  let e := cohomologyPresheafObjIsoRightDerivedSections.{u + 1} J ((F).obj P) (n + 1) X
  refine AddCommGrpCat.isZero_iff_subsingleton.2 ⟨fun a b => ?_⟩
  apply (ConcreteCategory.bijective_of_isIso e.inv).injective
  exact (injective_underlying_H_succ_eq_zero k P X n (e.inv a)).trans
    (injective_underlying_H_succ_eq_zero k P X n (e.inv b)).symm

private theorem quasiIso_sectionsAt_underlying_of_resolution
    (X : SmoothSite S) (I : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ)
    (hI : ∀ i, Injective (I.X i)) {K : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℤ}
    (a : ((F).mapHomologicalComplex c).obj I ⟶ K) [QuasiIso a] (hK : K.IsKInjective) :
    QuasiIso (((sectionsAt k X).mapHomologicalComplex c).map a) := by
  let A := AddCommGrpCat.{u + 1}
  let E : Sheaf J A ⥤ A := sectionsAt k X
  let : HasDerivedCategory (Sheaf J A) := HasDerivedCategory.standard _
  let : HasDerivedCategory A := HasDerivedCategory.standard A
  let : HasExt.{u + 1} (Sheaf J A) := hasExt_of_enoughInjectives _
  let H := E.mapHomologicalComplex c ⋙ DerivedCategory.Q
  let W := HomologicalComplex.quasiIso (Sheaf J A) c
  let : H.HasRightDerivedFunctor W := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q E
  let R := H.totalRightDerived DerivedCategory.Q W
  let α := H.totalRightDerivedUnit DerivedCategory.Q W
  obtain ⟨d, hd⟩ := SmoothSite.exists_nat_topologicalKrullDim_le k X
  have hd' : topologicalKrullDim X.left < (d + 1 : ℕ) :=
    hd.trans_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self d)))
  have hA : IsIso (α.app (((F).mapHomologicalComplex c).obj I)) := by
    apply Functor.isIso_app_of_rightAcyclic_of_isZero_rightDerived E (d + 1)
      (isZero_rightDerived_sectionsAt_of_krullDim_lt k X (d + 1) hd') R α
    intro i n hn
    let : Injective (I.X i) := hI i
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact isZero_rightDerived_sectionsAt_underlying_injective k X (I.X i) n
  exact Functor.quasiIso_map_of_isIso_rightDerivedUnit_app_Q E R α a hK hA

/-- On the original ordinary presheaves, a K-injective resolution of the
underlying sheaf complex of transfer injectives is already a quasi-isomorphism. -/
theorem quasiIso_underlyingPresheaf_of_injectiveTerms
    (I : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ)
    (hI : ∀ i, Injective (I.X i)) {K : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℤ}
    (a : ((F).mapHomologicalComplex c).obj I ⟶ K) [QuasiIso a] (hK : K.IsKInjective) :
    QuasiIso (((U).mapHomologicalComplex c).map a) := by
  apply (HomologicalComplex.quasiIso_iff_evaluation _).2
  intro X
  exact quasiIso_sectionsAt_underlying_of_resolution k X.unop I hI a hK

end AlgebraicGeometry.SheafWithTransfers
