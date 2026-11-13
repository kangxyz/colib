/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.Evaluation
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedAdjunction
import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerivedQ

/-!
# Derived torus sections commute with derived forget

At each smooth object, the established evaluation theorem identifies
evaluation after torus sections with evaluation at the product. Exact
presheaf evaluations detect quasi-isomorphisms, so these comparisons
give the derived forget comparison on unbounded complexes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme
open Stacks.Injectives.KInjectiveResolution

universe u w₁ w₂ w₃

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w₁} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w₂} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w₃} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Abelian groups in the coefficient universe of transfer presheaves. -/
abbrev LargeAb (_ : Type u) := AddCommGrpCat.{u + 1}

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "Ab" => LargeAb k

local notation "S" => Spec (CommRingCat.of k)
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject S
local notation "c" => ComplexShape.up ℤ
set_option quotPrecheck false in
local notation "U" => (SheafWithTransfers.forget k : NST ⥤ PST)
set_option quotPrecheck false in
local notation "T" => (PresheafWithTransfers.withParameterFunctor Gₘ : PST ⥤ PST)
set_option quotPrecheck false in
local notation "B" => (torusSectionsFunctor k : NST ⥤ NST)
set_option quotPrecheck false in
local notation "W" => HomologicalComplex.quasiIso NST c
set_option quotPrecheck false in
local notation "Qₛ" => DerivedCategory.Q (C := NST)
set_option quotPrecheck false in
local notation "Qₚ" => DerivedCategory.Q (C := PST)
set_option quotPrecheck false in
local notation "Qₐ" => DerivedCategory.Q (C := Ab)

/-- Evaluate a transfer presheaf on its original signed correspondence object. -/
abbrev presheafEvaluation (X : Cor k) : PST ⥤ Ab :=
  PresheafWithTransfers.forget ⋙ (CategoryTheory.evaluation (Cor k)ᵒᵖ Ab).obj (op X)

private def transferEvaluationUnderlyingIso (X : SmoothSite (Spec (.of k))) :
    transferEvaluationFunctor k X ≅ U ⋙ presheafEvaluation k (Cor.mk X) :=
  NatIso.ofComponents (fun F => (transferSectionsEquiv k (Cor.mk X) F).toAddCommGrpIso)
    (fun {_ _} f => by
      ext a
      exact transferSectionsEquiv_comp k (Cor.mk X) a f)

omit [HasDerivedCategory NST]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology S) Ab)] in
private theorem isIso_of_presheafEvaluation {K L : DerivedCategory PST} (f : K ⟶ L)
    (h : ∀ X : Cor k, IsIso ((presheafEvaluation k X).mapDerivedCategory.map f)) :
    IsIso f := by
  apply (DerivedCategory.isIso_iff _ f).2
  intro n
  let V := (PresheafWithTransfers.forget : PST ⥤ (Cor k)ᵒᵖ ⥤ Ab)
  let q := (DerivedCategory.homologyFunctor PST n).map f
  let : V.ReflectsIsomorphisms :=
    (additiveFunctor (Cor k)ᵒᵖ Ab).fullyFaithfulι.reflectsIsomorphisms
  let : IsIso (V.map q) := (NatTrans.isIso_iff_isIso_app (V.map q)).2 (fun X =>
    ((presheafEvaluation k X.unop).isIso_mapDerivedCategory_map_iff f).1 (h X.unop) n)
  exact isIso_of_reflects_iso q V

private def forgetEvaluationSourceIso (X : SmoothSite (Spec (.of k))) :
    forgetComplexToDerived k ⋙ (presheafEvaluation k (Cor.mk X)).mapDerivedCategory ≅
      transferEvaluationComplexToDerived k X :=
  mapDerivedCategorySourceIsoQ U (presheafEvaluation k (Cor.mk X)) ≪≫
    Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (transferEvaluationUnderlyingIso k X).symm c) Qₐ

private def forgetEvaluationComparisonUnit (X : SmoothSite (Spec (.of k))) :
    (forgetComplexToDerived k ⋙ (presheafEvaluation k (Cor.mk X)).mapDerivedCategory) ⟶
      Qₛ ⋙ (forgetDerivedFunctor k ⋙ (presheafEvaluation k (Cor.mk X)).mapDerivedCategory) :=
  Functor.whiskerRight (forgetDerivedUnit k) (presheafEvaluation k (Cor.mk X)).mapDerivedCategory ≫
    (Functor.associator Qₛ _ _).hom

private instance forgetEvaluation_isRightDerived (X : SmoothSite (Spec (.of k))) :
    Functor.IsRightDerivedFunctor
      (forgetDerivedFunctor k ⋙ (presheafEvaluation k (Cor.mk X)).mapDerivedCategory)
      (forgetEvaluationComparisonUnit k X) W := by
  apply (isRightDerivedFunctor_iff_isIso_app_of_isKInjective Qₛ _ _
    (invertsQuasiIsoOfIsKInjective_comp (invertsQuasiIso_mapHomologicalComplex_comp_Q U)
      (presheafEvaluation k (Cor.mk X)).mapDerivedCategory)).2
  intro I hI
  let : IsIso ((forgetDerivedUnit k).app I) :=
    isIso_app_of_isKInjective Qₛ _ _ (invertsQuasiIso_mapHomologicalComplex_comp_Q U) I hI
  change IsIso ((presheafEvaluation k (Cor.mk X)).mapDerivedCategory.map
    ((forgetDerivedUnit k).app I) ≫ (Functor.associator Qₛ _ _).hom.app I)
  infer_instance

/-- Each exact presheaf evaluation of derived forget is the actual derived
transfer evaluation. The comparison is induced by the original sections equivalence. -/
@[no_expose]
def forgetDerivedEvaluationIso (X : SmoothSite (Spec (.of k))) :
    forgetDerivedFunctor k ⋙ (presheafEvaluation k (Cor.mk X)).mapDerivedCategory ≅
      transferEvaluationDerivedFunctor k X :=
  Functor.rightDerivedNatIso _ _ (forgetEvaluationComparisonUnit k X)
    (transferEvaluationDerivedUnit k X) W (forgetEvaluationSourceIso k X)

omit [HasDerivedCategory PST] in
private theorem isIso_evaluationDerivedUnit_app_torus (X : SmoothSite (Spec (.of k)))
    (I : CochainComplex NST ℤ) [I.IsKInjective] :
    IsIso ((transferEvaluationDerivedUnit k X).app (((B).mapHomologicalComplex c).obj I)) := by
  have hI : IsIso ((torusSectionsEvaluationDerivedUnit k X).app I) :=
    isIso_app_of_isKInjective Qₛ _ _ (invertsQuasiIso_mapHomologicalComplex_comp_Q
      (B ⋙ transferEvaluationFunctor k X)) I inferInstance
  have hR : IsIso ((torusSectionsDerivedUnit k).app I) :=
    isIso_app_of_isKInjective Qₛ _ _
      (invertsQuasiIso_mapHomologicalComplex_comp_Q B) I inferInstance
  let b := (transferEvaluationDerivedFunctor k X).map ((torusSectionsDerivedUnit k).app I)
  let : IsIso b := inferInstance
  rw [torusSectionsEvaluationDerivedUnit_app] at hI
  change IsIso ((transferEvaluationDerivedUnit k X).app (((B).mapHomologicalComplex c).obj I) ≫
    b) at hI
  exact IsIso.of_isIso_comp_right _ b

/-- The derived forget comparison is invertible on the actual torus sections
of a K-injective complex, detected at each smooth evaluation. -/
theorem isIso_forgetDerivedUnit_app_torus (I : CochainComplex NST ℤ) [I.IsKInjective] :
    IsIso ((forgetDerivedUnit k).app (((B).mapHomologicalComplex c).obj I)) := by
  let J := ((B).mapHomologicalComplex c).obj I
  apply isIso_of_presheafEvaluation k
  intro X
  let e := forgetDerivedEvaluationIso k X.toSmoothSite
  let E := (presheafEvaluation k X).mapDerivedCategory
  let : (forgetDerivedFunctor k ⋙ E).IsRightDerivedFunctor
      (forgetEvaluationComparisonUnit k X.toSmoothSite) W :=
    forgetEvaluation_isRightDerived k X.toSmoothSite
  have h := Functor.rightDerivedNatTrans_app
    (forgetDerivedFunctor k ⋙ E) (transferEvaluationDerivedFunctor k X.toSmoothSite)
    (forgetEvaluationComparisonUnit k X.toSmoothSite)
    (transferEvaluationDerivedUnit k X.toSmoothSite)
    W (forgetEvaluationSourceIso k X.toSmoothSite).hom J
  change (forgetEvaluationComparisonUnit k X.toSmoothSite).app J ≫ e.hom.app ((Qₛ).obj J) =
    (forgetEvaluationSourceIso k X.toSmoothSite).hom.app J ≫
      (transferEvaluationDerivedUnit k X.toSmoothSite).app J at h
  have hunit : (forgetEvaluationComparisonUnit k X.toSmoothSite).app J =
      E.map ((forgetDerivedUnit k).app J) := by
    change E.map ((forgetDerivedUnit k).app J) ≫ 𝟙 _ = _
    exact Category.comp_id _
  rw [hunit] at h
  let : IsIso ((transferEvaluationDerivedUnit k X.toSmoothSite).app J) :=
    isIso_evaluationDerivedUnit_app_torus k X.toSmoothSite I
  let : IsIso (E.map ((forgetDerivedUnit k).app J) ≫ e.hom.app ((Qₛ).obj J)) :=
    h.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_right _ (e.hom.app ((Qₛ).obj J))

/-- The comparison unit for deriving the composite of torus sections and forget. -/
def torusForgetCompositionUnit :
    (B ⋙ U).mapHomologicalComplex c ⋙ Qₚ ⟶
      Qₛ ⋙ (torusSectionsDerivedFunctor k ⋙ forgetDerivedFunctor k) :=
  Functor.whiskerLeft ((B).mapHomologicalComplex c) (forgetDerivedUnit k) ≫
    Functor.whiskerRight (torusSectionsDerivedUnit k) (forgetDerivedFunctor k)

instance torusForgetComposition_isRightDerived :
    (torusSectionsDerivedFunctor k ⋙ forgetDerivedFunctor k).IsRightDerivedFunctor
      (torusForgetCompositionUnit k) W := by
  apply (isRightDerivedFunctor_iff_isIso_app_of_isKInjective Qₛ _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q (B ⋙ U))).2
  intro I hI
  let : I.IsKInjective := hI
  let : IsIso ((forgetDerivedUnit k).app (((B).mapHomologicalComplex c).obj I)) :=
    isIso_forgetDerivedUnit_app_torus k I
  let : IsIso ((torusSectionsDerivedUnit k).app I) :=
    isIso_app_of_isKInjective Qₛ _ _ (invertsQuasiIso_mapHomologicalComplex_comp_Q B) I hI
  change IsIso ((forgetDerivedUnit k).app (((B).mapHomologicalComplex c).obj I) ≫
    (forgetDerivedFunctor k).map ((torusSectionsDerivedUnit k).app I))
  infer_instance

/-- The comparison unit for deriving forget and then reindexing the presheaf. -/
def torusTensorDerivedRightUnit :
    (U ⋙ T).mapHomologicalComplex c ⋙ Qₚ ⟶ Qₛ ⋙ torusTensorDerivedRight k :=
  (mapDerivedCategorySourceIsoQ U T).inv ≫
    Functor.whiskerRight (forgetDerivedUnit k) (T).mapDerivedCategory ≫
      (Functor.associator Qₛ _ _).hom

private instance torusTensorDerivedRight_isRightDerived :
    (torusTensorDerivedRight k).IsRightDerivedFunctor (torusTensorDerivedRightUnit k) W := by
  apply (isRightDerivedFunctor_iff_isIso_app_of_isKInjective Qₛ _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q (U ⋙ T))).2
  intro I hI
  let : IsIso ((forgetDerivedUnit k).app I) :=
    isIso_app_of_isKInjective Qₛ _ _ (invertsQuasiIso_mapHomologicalComplex_comp_Q U) I hI
  change IsIso ((mapDerivedCategorySourceIsoQ U T).inv.app I ≫
    ((T).mapDerivedCategory.map ((forgetDerivedUnit k).app I) ≫
      (Functor.associator Qₛ _ _).hom.app I))
  infer_instance

/-- The actual right-derived torus sections followed by derived forget agree
with derived forget followed by exact presheaf reindexing. -/
@[no_expose]
def torusSectionsDerivedForgetIso :
    torusSectionsDerivedFunctor k ⋙ forgetDerivedFunctor k ≅ torusTensorDerivedRight k :=
  Functor.rightDerivedNatIso _ _ (torusForgetCompositionUnit k) (torusTensorDerivedRightUnit k) W
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (torusSectionsUnderlyingIso k).symm c) Qₚ)

/-- The forget comparison is induced by the original comparison of the two
parameter functors on complexes. -/
@[reassoc]
theorem torusSectionsDerivedForgetIso_hom_app_Q_obj (K : CochainComplex NST ℤ) :
    (torusForgetCompositionUnit k).app K ≫ (torusSectionsDerivedForgetIso k).hom.app ((Qₛ).obj K) =
      (Qₚ).map ((NatIso.mapHomologicalComplex (torusSectionsUnderlyingIso k).symm c).hom.app K) ≫
        (torusTensorDerivedRightUnit k).app K := by
  unfold torusSectionsDerivedForgetIso
  exact Functor.rightDerivedNatTrans_app _ _ (torusForgetCompositionUnit k)
    (torusTensorDerivedRightUnit k) W _ K

omit [HasDerivedCategory Ab] [HasExt (Sheaf (SmoothSite.nisnevichTopology S) Ab)] in
/-- The composite derived unit applies the two original units in order. -/
theorem torusForgetCompositionUnit_app (K : CochainComplex NST ℤ) :
    (torusForgetCompositionUnit k).app K =
      (forgetDerivedUnit k).app (((B).mapHomologicalComplex c).obj K) ≫
        (forgetDerivedFunctor k).map ((torusSectionsDerivedUnit k).app K) := rfl

omit [HasDerivedCategory Ab] [HasExt (Sheaf (SmoothSite.nisnevichTopology S) Ab)] in
/-- Exact reindexing takes the derived forget unit through its original
complex factorization. -/
theorem torusTensorDerivedRightUnit_app (K : CochainComplex NST ℤ) :
    (torusTensorDerivedRightUnit k).app K =
      (T).mapDerivedCategoryFactors.inv.app (((U).mapHomologicalComplex c).obj K) ≫
        (T).mapDerivedCategory.map ((forgetDerivedUnit k).app K) := by
  unfold torusTensorDerivedRightUnit mapDerivedCategorySourceIsoQ
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Category.assoc, Category.comp_id]
  exact congrArg (_ ≫ ·) (Category.id_comp
    ((T).mapDerivedCategory.map ((forgetDerivedUnit k).app K)))

end AlgebraicGeometry.SheafWithTransfers
