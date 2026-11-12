/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.OrdinaryComparison
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.TorusEvaluation
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.TorusInjectiveDirectImage
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.ParameterProduct.Restriction
import Colib.Algebra.Homology.DerivedCategory.Ext.RightDerived
import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Original.MapAtBase
import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso
import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf

/-!
# Acyclicity of torus sections of transfer-injective coefficients

On the small Nisnevich site the reindexed coefficient is the actual
direct image along the torus projection. Every higher image of a
transfer-injective coefficient vanishes, as do its higher sections on
the source. The derived composition gives acyclicity of the resulting
coefficient for evaluation at the original smooth scheme.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme
open Stacks.Cohomology.FreeYonedaUnivLE

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "G" => SmoothSite.multiplicativeGroupObject S

variable [HasExt.{u + 1}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

private theorem torusSections_underlying_H_succ_isZero
    (I : SheafWithTransfers.{u + 1} k) [Injective I] (X : SmoothSite S) (n : ℕ) :
    IsZero ((cohomologyPresheaf.{u + 1, u + 1}
      ((toSheaf k).obj ((torusSectionsFunctor k).obj I)) (n + 1)).obj (op X)) := by
  let Y := SmoothSite.product X G
  let p := (SmoothSite.productFst X G).left
  let JX := EtaleSeparatedFiniteType.nisnevichTopology X.left
  let JY := EtaleSeparatedFiniteType.nisnevichTopology Y.left
  let A := AddCommGrpCat.{u + 1}
  let : HasDerivedCategory (Sheaf JX A) := HasDerivedCategory.standard (Sheaf JX A)
  let : HasDerivedCategory (Sheaf JY A) := HasDerivedCategory.standard (Sheaf JY A)
  let : HasDerivedCategory A := HasDerivedCategory.standard A
  let : HasExt.{u + 1} (Sheaf JX A) := hasExt_of_enoughInjectives _
  let FY := (EtaleSeparatedFiniteType.restrict Y A).obj ((toSheaf k).obj I)
  let FX := (toSheaf k).obj ((torusSectionsFunctor k).obj I)
  let P := EtaleSeparatedFiniteType.directImage p
  let X₀ := EtaleSeparatedFiniteType.identityObject X
  let Y₀ := EtaleSeparatedFiniteType.identityObject Y
  let ΓX := (sheafSections JX A).obj (op X₀)
  let ΓY := (sheafSections JY A).obj (op Y₀)
  let e₀ := (EtaleSeparatedFiniteType.cohomologyAtBaseEquiv X FX (n + 1)).toAddCommGrpIso
  let e₁ := cohomologyPresheafObjIsoRightDerivedSections.{u + 1} JX
    ((EtaleSeparatedFiniteType.restrict X A).obj FX) (n + 1) X₀
  let eF : (EtaleSeparatedFiniteType.restrict X A).obj FX ≅ P.obj FY :=
    (EtaleSeparatedFiniteType.restrict X A).mapIso ((torusSectionsToSheafIso k).app I) ≪≫
      (EtaleSeparatedFiniteType.restrictParameterSectionsIso X G).app ((toSheaf k).obj I)
  let : P.PreservesInjectiveObjects :=
    { injective_obj h := (EtaleSeparatedFiniteType.imageAdjunction p).map_injective _ h }
  have hP := restricted_injective_directImage_rightAcyclic k I X
  let e₂ := (ΓX.rightDerived (n + 1)).mapIso eF
  let H := DerivedCategory.Plus.homologyFunctor A ((n + 1 : ℕ) : ℤ)
  let Q := DerivedCategory.Plus.singleFunctor (Sheaf JY A) 0
  let Z := Q.obj FY
  let α := P.rightDerivedFunctorPlusUnith
  let b := P.rightDerivedFunctorPlus
  let z := (HomotopyCategory.Plus.singleFunctor (Sheaf JY A) 0).obj FY
  let F := P.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
  let W := HomotopyCategory.Plus.quasiIso (Sheaf JY A)
  let β := F.totalRightDerivedUnit DerivedCategory.Plus.Qh W
  let γ := b.rightDerivedDesc α W _ β
  let : IsIso γ := (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc b α W _ β).1
    inferInstance
  let : IsIso (β.app z) := hP
  let : IsIso (α.app z) :=
    (isIso_comp_right_iff (α.app z) (γ.app (DerivedCategory.Plus.Qh.obj z))).1
      (by rw [Functor.rightDerived_fac_app b α W _ β]; infer_instance)
  let eb : (DerivedCategory.Plus.singleFunctor (Sheaf JX A) 0).obj (P.obj FY) ≅ b.obj Z :=
    (CategoryTheory.Functor.mapSingleFunctorCompQhIso P).symm.app FY ≪≫
      asIso (α.app z) ≪≫
      b.mapIso ((DerivedCategory.Plus.singleFunctorIsoCompQh (Sheaf JY A) 0).app FY).symm
  let eComp := (P.rightDerivedFunctorPlusCompIso ΓX).app Z
  let e₃ : ((ΓX.rightDerived (n + 1)).obj (P.obj FY)) ≅
      (((P ⋙ ΓX).rightDerived (n + 1)).obj FY) :=
    (Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandardObj ΓX
      (P.obj FY) (n + 1)).symm ≪≫
        H.mapIso (ΓX.rightDerivedFunctorPlus.mapIso eb) ≪≫
        H.mapIso eComp.symm ≪≫
        Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandardObj (P ⋙ ΓX) FY (n + 1)
  let eV := EtaleSeparatedFiniteType.baseChangeIdentityIso (SmoothSite.productFst X G)
  let eΓ : P ⋙ ΓX ≅ ΓY := NatIso.ofComponents
    (fun F => F.obj.mapIso eV.symm.op) (fun f => (f.hom.naturality eV.inv.op).symm)
  let e₄ := (Functor.rightDerivedIsoOfNatIso eΓ (n + 1)).app FY
  exact (restricted_injective_cohomology_isZero k I Y n Y₀).of_iso
    (e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄)

/-- Evaluation of the actual torus sections of an injective transfer
sheaf has no positive derived functors. -/
theorem isZero_rightDerived_transferEvaluation_torusSections_injective
    (X : SmoothSite S) (I : SheafWithTransfers.{u + 1} k) [Injective I] (n : ℕ) :
    IsZero (((transferEvaluationFunctor k X).rightDerived (n + 1)).obj
      ((torusSectionsFunctor k).obj I)) := by
  let F := (torusSectionsFunctor k).obj I
  let R := (transferRepresentable k).obj (Cor.mk X)
  let : HasExt.{u + 1} (SheafWithTransfers.{u + 1} k) := hasExt_of_enoughInjectives _
  let e := (transferExtEquiv k X F (n + 1)).symm.trans
    ((injectiveResolution F).extRightDerivedAddEquiv R (n + 1))
  exact (torusSections_underlying_H_succ_isZero k I X n).of_iso e.symm.toAddCommGrpIso

end AlgebraicGeometry.SheafWithTransfers
