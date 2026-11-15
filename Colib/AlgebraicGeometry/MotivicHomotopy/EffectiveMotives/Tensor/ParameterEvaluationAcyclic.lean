/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.TorusInjectiveDirectImage
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.ParameterProduct.Restriction
import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Original.MapAtBase
import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso
import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.AbelianHigherDirectImageSheafification
import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf

/-!
# Acyclic evaluation after smooth parameter reindexing

Small-site direct image of a restricted transfer injective has vanishing
higher images. Its composite with evaluation at the base is evaluation at
the source of the direct image. This gives the acyclicity of smooth
parameter sections for transfer evaluation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme
open Stacks.Cohomology.FreeYonedaUnivLE
open Stacks.Cohomology.SheafifiedHigherDirectImage

universe u

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k]

local notation "Base(" K ")" => Spec (CommRingCat.of K)
/-- Ordinary coefficients in the universe of the smooth transfer site. -/
abbrev SmoothParameterAb (_ : Type u) := AddCommGrpCat.{u + 1}
local notation "Ab(" K ")" => SmoothParameterAb K

variable [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology Base(k)) Ab(k))]

/-- Restricting a transfer injective to the small Nisnevich site of a smooth
scheme gives an acyclic coefficient for direct image to another smooth scheme. -/
theorem restricted_injective_directImage_rightAcyclic_of_smooth
    (I : SheafWithTransfers.{u + 1} k) [Injective I] {Y X : SmoothSite Base(k)} (f : Y ⟶ X)
    [HasDerivedCategory (Sheaf (EtaleSeparatedFiniteType.nisnevichTopology X.left) Ab(k))]
    [HasDerivedCategory (Sheaf (EtaleSeparatedFiniteType.nisnevichTopology Y.left) Ab(k))] :
    (EtaleSeparatedFiniteType.directImage f.left).rightAcyclic
      ((EtaleSeparatedFiniteType.restrict Y Ab(k)).obj ((toSheaf k).obj I)) := by
  let JX := EtaleSeparatedFiniteType.nisnevichTopology X.left
  let JY := EtaleSeparatedFiniteType.nisnevichTopology Y.left
  let FY := (EtaleSeparatedFiniteType.restrict Y Ab(k)).obj ((toSheaf k).obj I)
  let q := EtaleSeparatedFiniteType.baseChange f.left
  let : q.IsContinuous JX JY := EtaleSeparatedFiniteType.baseChange_isContinuous f.left
  apply (CategoryTheory.rightAcyclic_iff_isZero_rightDerived
    (EtaleSeparatedFiniteType.directImage f.left) FY).2
  intro m hm
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  let D := pushforwardCohomologyPresheaf (K := JY) Ab(k) q
  have hD : IsZero ((D.rightDerived (n + 1)).obj FY) := (Functor.isZero_iff _).2 (by
    intro V
    let e := (pushforwardCohomologyPresheafEvaluationIso Ab(k) q (n + 1) V.unop).app FY
    exact (restricted_injective_cohomology_isZero k I Y n (q.obj V.unop)).of_iso e.symm)
  exact ((presheafToSheaf JX Ab(k)).map_isZero hD).of_iso
    ((rightDerivedPushforwardIso Ab(k) q (n + 1)).app FY)

/-- A coefficient whose restriction is the direct image of a restricted
transfer injective has zero positive cohomology at the smooth base. -/
theorem cohomologyPresheaf_obj_isZero_of_restrictIso_directImage_injective
    (I : SheafWithTransfers.{u + 1} k) [Injective I] {Y X : SmoothSite Base(k)} (f : Y ⟶ X)
    (FX : Sheaf (SmoothSite.nisnevichTopology Base(k)) Ab(k))
    (eF : (EtaleSeparatedFiniteType.restrict X Ab(k)).obj FX ≅
      (EtaleSeparatedFiniteType.directImage f.left).obj
        ((EtaleSeparatedFiniteType.restrict Y Ab(k)).obj ((toSheaf k).obj I))) (n : ℕ) :
    IsZero ((cohomologyPresheaf.{u + 1, u + 1} FX (n + 1)).obj (op X)) := by
  let p := f.left
  let JX := EtaleSeparatedFiniteType.nisnevichTopology X.left
  let JY := EtaleSeparatedFiniteType.nisnevichTopology Y.left
  let : HasDerivedCategory (Sheaf JX Ab(k)) := HasDerivedCategory.standard (Sheaf JX Ab(k))
  let : HasDerivedCategory (Sheaf JY Ab(k)) := HasDerivedCategory.standard (Sheaf JY Ab(k))
  let : HasDerivedCategory Ab(k) := HasDerivedCategory.standard Ab(k)
  let : HasExt.{u + 1} (Sheaf JX Ab(k)) := hasExt_of_enoughInjectives _
  let FY := (EtaleSeparatedFiniteType.restrict Y Ab(k)).obj ((toSheaf k).obj I)
  let P := EtaleSeparatedFiniteType.directImage p
  let X₀ := EtaleSeparatedFiniteType.identityObject X
  let Y₀ := EtaleSeparatedFiniteType.identityObject Y
  let ΓX := (sheafSections JX Ab(k)).obj (op X₀)
  let ΓY := (sheafSections JY Ab(k)).obj (op Y₀)
  let e₀ := (EtaleSeparatedFiniteType.cohomologyAtBaseEquiv X FX (n + 1)).toAddCommGrpIso
  let e₁ := cohomologyPresheafObjIsoRightDerivedSections.{u + 1} JX
    ((EtaleSeparatedFiniteType.restrict X Ab(k)).obj FX) (n + 1) X₀
  let : P.PreservesInjectiveObjects :=
    { injective_obj h := (EtaleSeparatedFiniteType.imageAdjunction p).map_injective _ h }
  have hP := restricted_injective_directImage_rightAcyclic_of_smooth k I f
  let e₂ := (ΓX.rightDerived (n + 1)).mapIso eF
  let H := DerivedCategory.Plus.homologyFunctor Ab(k) ((n + 1 : ℕ) : ℤ)
  let Q := DerivedCategory.Plus.singleFunctor (Sheaf JY Ab(k)) 0
  let Z := Q.obj FY
  let α := P.rightDerivedFunctorPlusUnith
  let b := P.rightDerivedFunctorPlus
  let z := (HomotopyCategory.Plus.singleFunctor (Sheaf JY Ab(k)) 0).obj FY
  let F := P.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
  let W := HomotopyCategory.Plus.quasiIso (Sheaf JY Ab(k))
  let β := F.totalRightDerivedUnit DerivedCategory.Plus.Qh W
  let γ := b.rightDerivedDesc α W _ β
  let : IsIso γ := (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc b α W _ β).1
    inferInstance
  let : IsIso (β.app z) := hP
  let : IsIso (α.app z) :=
    (isIso_comp_right_iff (α.app z) (γ.app (DerivedCategory.Plus.Qh.obj z))).1
      (by rw [Functor.rightDerived_fac_app b α W _ β]; infer_instance)
  let eb : (DerivedCategory.Plus.singleFunctor (Sheaf JX Ab(k)) 0).obj (P.obj FY) ≅ b.obj Z :=
    (CategoryTheory.Functor.mapSingleFunctorCompQhIso P).symm.app FY ≪≫
      asIso (α.app z) ≪≫
      b.mapIso ((DerivedCategory.Plus.singleFunctorIsoCompQh (Sheaf JY Ab(k)) 0).app FY).symm
  let eComp := (P.rightDerivedFunctorPlusCompIso ΓX).app Z
  let e₃ : ((ΓX.rightDerived (n + 1)).obj (P.obj FY)) ≅
      (((P ⋙ ΓX).rightDerived (n + 1)).obj FY) :=
    (Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandardObj ΓX
      (P.obj FY) (n + 1)).symm ≪≫
        H.mapIso (ΓX.rightDerivedFunctorPlus.mapIso eb) ≪≫
        H.mapIso eComp.symm ≪≫
        Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandardObj (P ⋙ ΓX) FY (n + 1)
  let eV := EtaleSeparatedFiniteType.baseChangeIdentityIso f
  let eΓ : P ⋙ ΓX ≅ ΓY := NatIso.ofComponents
    (fun F => F.obj.mapIso eV.symm.op) (fun g => (g.hom.naturality eV.inv.op).symm)
  let e₄ := (Functor.rightDerivedIsoOfNatIso eΓ (n + 1)).app FY
  exact (restricted_injective_cohomology_isZero k I Y n Y₀).of_iso
    (e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄)

end AlgebraicGeometry.SheafWithTransfers
