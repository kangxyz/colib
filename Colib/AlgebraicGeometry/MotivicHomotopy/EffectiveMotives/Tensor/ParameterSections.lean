/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.ParameterEvaluationAcyclic
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.Pushforward
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

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]

/-- The original integral parameter product agrees with the smooth parameter
product on graph correspondences. -/
def parameterProductGraphIso (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom] :
    graphFunctor k ⋙ parameterProduct T ≅
      SmoothSite.Contraction.parameterProduct T ⋙ graphFunctor k :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    change (parameterProduct T).map ((graphFunctor k).map f) ≫ 𝟙 _ =
      𝟙 _ ≫ (graphFunctor k).map (SmoothSite.productMap f (𝟙 T))
    rw [Category.comp_id, Category.id_comp]
    exact parameterProduct_graph T f)

end AlgebraicGeometry.Cor

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

/-- Underlying presheaves of the reindexed coefficients are the ordinary
smooth parameter sections. -/
def parameterPrecomposeUnderlyingIso (P : PST(k)) :
    (toPresheaf k).obj ((additivePrecompose F).obj P) ≅
      (SmoothSite.Contraction.parameterProduct T).op ⋙ (toPresheaf k).obj P :=
  NatIso.ofComponents (fun X => P.obj.mapIso ((NatIso.op e.symm).app X)) (by
    intro X Y f
    let d := NatIso.op e.symm
    change P.obj.map ((Cor.graphFunctor k ⋙ F).op.map f) ≫ P.obj.map (d.hom.app Y) =
      P.obj.map (d.hom.app X) ≫
        P.obj.map ((SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k).op.map f)
    rw [← P.obj.map_comp, ← P.obj.map_comp, d.hom.naturality])

/-- Reindex along the correspondence functor while retaining the Nisnevich
sheaf condition given by ordinary parameter continuity. -/
def parameterSectionsOfGraphIso : NST(k) ⥤ NST(k) :=
  (IsNisnevichSheaf k).lift (SheafWithTransfers.forget k ⋙ additivePrecompose F) (fun I => by
    apply (Presheaf.isSheaf_of_iso_iff (parameterPrecomposeUnderlyingIso e I.obj)).2
    exact (SmoothSite.Contraction.parameterProduct T).op_comp_isSheaf_of_isSheaf _ _ _ I.property)

instance : (parameterSectionsOfGraphIso e).Additive where
  map_add := by
    intro P Q f g
    apply ObjectProperty.hom_ext
    rfl

/-- Forgetting transfers gives ordinary parameter sections, with the
original coefficient restrictions. -/
def parameterSectionsOfGraphIsoToSheaf :
    parameterSectionsOfGraphIso e ⋙ toSheaf k ≅
      toSheaf k ⋙ (SmoothSite.Contraction.parameterProduct T).sheafPushforwardContinuous
        Ab(k) Nis(k) Nis(k) :=
  NatIso.ofComponents (fun I => ObjectProperty.isoMk _ (parameterPrecomposeUnderlyingIso e I.obj))
    (fun f => by
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext X
      exact (f.hom.hom.naturality ((NatIso.op e.symm).hom.app X)).symm)

/-- The original integral parameter sections use the same reindexed
coefficients and signed transfers. -/
def parameterSectionsOfGraphIsoIntegral (T : SmoothSite Base(k)) [GeometricallyIntegral T.hom] :
    parameterSectionsOfGraphIso (Cor.parameterProductGraphIso T) ≅ parameterSectionsFunctor k T :=
  Iso.refl _

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
