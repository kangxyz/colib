/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.ParameterEvaluationAcyclic
public import Colib.AlgebraicGeometry.SheavesWithTransfers.ParameterSections
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.OrdinaryComparison
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.TorusEvaluation
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.ParameterNaturality
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedAdjunction
import Colib.Algebra.Homology.DerivedCategory.Ext.RightDerived

/-!
# Parameter sections of Nisnevich sheaves with transfers

An additive correspondence functor agreeing with the smooth parameter
product on graphs reindexes sheaves with transfers. The comparison on
graphs identifies the reindexed sheaf with ordinary parameter sections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "Base(" K ")" => Spec (CommRingCat.of K)
local notation "Nis(" K ")" => SmoothSite.nisnevichTopology Base(K)
local notation "Ab(" K ")" => SmoothParameterAb K
local notation "PST(" K ")" => LargePresheaves K
local notation "NST(" K ")" => LargeSheaves K

variable {T : SmoothSite Base(k)} {F : Cor k ⥤ Cor k} [F.Additive]
  (e : Cor.graphFunctor k ⋙ F ≅
    SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)

variable [HasExt.{u + 1} (Sheaf Nis(k) Ab(k))]

/-- Transfer evaluation at a smooth scheme has zero positive derived
functors on the reindexed coefficient of a transfer injective. -/
theorem isZero_rightDerived_transferEvaluation_parameterSectionsOfGraphIso_injective
    (X : SmoothSite Base(k)) (I : NST(k)) [Injective I] (n : ℕ) :
    IsZero (((transferEvaluationFunctor k X).rightDerived (n + 1)).obj
      ((parameterSectionsOfGraphIso e).obj I)) := by
  let H := (parameterSectionsOfGraphIso e).obj I
  let R := (transferRepresentable k).obj (Cor.mk X)
  let : HasExt.{u + 1} NST(k) := hasExt_of_enoughInjectives _
  let b := (transferExtEquiv k X H (n + 1)).symm.trans
    ((injectiveResolution H).extRightDerivedAddEquiv R (n + 1))
  let eF := (EtaleSeparatedFiniteType.restrict X Ab(k)).mapIso
    ((parameterSectionsOfGraphIsoToSheaf e).app I) ≪≫
      (EtaleSeparatedFiniteType.restrictParameterSectionsIso X T).app ((toSheaf k).obj I)
  exact (cohomologyPresheaf_obj_isZero_of_restrictIso_directImage_injective k I
    (SmoothSite.productFst X T) _ eF n).of_iso b.symm.toAddCommGrpIso

end AlgebraicGeometry.SheafWithTransfers
