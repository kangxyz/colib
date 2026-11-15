/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.ParameterSections
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.PushforwardExactness
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedForgetComparison
import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerivedQ
import StacksFrontier.Algebra.Homology.DerivedCategory.TermwiseAcyclicComputesRightDerived
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

/-!
# Derived forget of smooth parameter sections

The right-derived sheaf parameter functor, followed by derived forget,
is exact presheaf reindexing of the derived underlying coefficient.
Represented evaluation of finite cohomological dimension detects the
comparison on the original cochain resolutions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme
open Stacks.Injectives.KInjectiveResolution

universe u w₁ w₂ w₃

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable {k : Type u} [Field k]
  [HasDerivedCategory.{w₁} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w₂} (SheafWithTransfers.{u + 1} k)]

local notation "Base(" K ")" => Spec (CommRingCat.of K)
local notation "PST(" K ")" => LargePresheaves K
local notation "NST(" K ")" => LargeSheaves K
local notation "Ab(" K ")" => LargeAb K
local notation "c" => ComplexShape.up ℤ

variable {T : SmoothSite Base(k)} {F : Cor k ⥤ Cor k} [F.Additive]
  (e : Cor.graphFunctor k ⋙ F ≅
    SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)

set_option quotPrecheck false in
local notation "Qs(" K ")" => DerivedCategory.Q (C := NST(K))
set_option quotPrecheck false in
local notation "Qp(" K ")" => DerivedCategory.Q (C := PST(K))
set_option quotPrecheck false in
local notation "W(" K ")" => HomologicalComplex.quasiIso NST(K) c
set_option quotPrecheck false in
local notation "U(" K ")" => (SheafWithTransfers.forget K : NST(K) ⥤ PST(K))
local notation "B(" comparison ")" => parameterSectionsOfGraphIso comparison
local notation "P(" F ")" => additivePrecompose F

omit [HasDerivedCategory PST(k)] in
instance : ((B(e)).mapHomologicalComplex c ⋙ Qs(k)).HasRightDerivedFunctor W(k) :=
  hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (B(e))

/-- The total right derived functor of smooth parameter sections on sheaves. -/
@[no_expose]
def parameterSectionsDerived : DerivedCategory NST(k) ⥤ DerivedCategory NST(k) :=
  ((B(e)).mapHomologicalComplex c ⋙ Qs(k)).totalRightDerived Qs(k) W(k)

/-- The original cochain comparison for right deriving smooth parameter sections. -/
@[no_expose]
def parameterSectionsDerivedUnit :
    (B(e)).mapHomologicalComplex c ⋙ Qs(k) ⟶ Qs(k) ⋙ parameterSectionsDerived e :=
  ((B(e)).mapHomologicalComplex c ⋙ Qs(k)).totalRightDerivedUnit Qs(k) W(k)

instance : (parameterSectionsDerived e).IsRightDerivedFunctor (parameterSectionsDerivedUnit e)
    W(k) := by
  dsimp only [parameterSectionsDerived, parameterSectionsDerivedUnit]
  infer_instance

private def parameterForgetCompositionUnit :
    (B(e) ⋙ U(k)).mapHomologicalComplex c ⋙ Qp(k) ⟶
      Qs(k) ⋙ (parameterSectionsDerived e ⋙ forgetDerivedFunctor k) :=
  Functor.whiskerLeft ((B(e)).mapHomologicalComplex c) (forgetDerivedUnit k) ≫
    Functor.whiskerRight (parameterSectionsDerivedUnit e) (forgetDerivedFunctor k)

private def reindexedForgetUnit :
    (U(k) ⋙ P(F)).mapHomologicalComplex c ⋙ Qp(k) ⟶
      Qs(k) ⋙ (forgetDerivedFunctor k ⋙ (P(F)).mapDerivedCategory) :=
  (mapDerivedCategorySourceIsoQ U(k) P(F)).inv ≫
    Functor.whiskerRight (forgetDerivedUnit k) (P(F)).mapDerivedCategory ≫
      (Functor.associator Qs(k) _ _).hom

private instance reindexedForget_isRightDerived :
    (forgetDerivedFunctor k ⋙ (P(F)).mapDerivedCategory).IsRightDerivedFunctor
      (reindexedForgetUnit (k := k) (F := F)) W(k) := by
  apply (isRightDerivedFunctor_iff_isIso_app_of_isKInjective Qs(k) _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q (U(k) ⋙ P(F)))).2
  intro I hI
  let : IsIso ((forgetDerivedUnit k).app I) :=
    isIso_app_of_isKInjective Qs(k) _ _ (invertsQuasiIso_mapHomologicalComplex_comp_Q U(k)) I hI
  change IsIso ((mapDerivedCategorySourceIsoQ U(k) P(F)).inv.app I ≫
    ((P(F)).mapDerivedCategory.map ((forgetDerivedUnit k).app I) ≫
      (Functor.associator Qs(k) _ _).hom.app I))
  infer_instance

variable [HasDerivedCategory.{w₃} Ab(k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology Base(k)) Ab(k))]

omit [HasDerivedCategory PST(k)] in
private theorem isIso_parameterEvaluationDerivedUnit (X : SmoothSite Base(k))
    (I : CochainComplex NST(k) ℤ) (hI : ∀ i, Injective (I.X i)) :
    IsIso ((transferEvaluationDerivedUnit k X).app (((B(e)).mapHomologicalComplex c).obj I)) := by
  obtain ⟨d, hd⟩ := exists_transferRepresentable_hasProjectiveDimensionLE k X
  let : HasProjectiveDimensionLE ((transferRepresentable k).obj (Cor.mk X)) d := hd
  apply Functor.isIso_app_of_rightAcyclic_of_isZero_rightDerived (transferEvaluationFunctor k X)
    (d + 1) (isZero_rightDerived_transferEvaluation_of_hasProjectiveDimensionLE k X d)
    (transferEvaluationDerivedFunctor k X)
  intro i p hp
  let : Injective (I.X i) := hI i
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  exact isZero_rightDerived_transferEvaluation_parameterSectionsOfGraphIso_injective e X (I.X i) n

omit [HasDerivedCategory NST(k)] [HasExt (Sheaf (SmoothSite.nisnevichTopology Base(k)) Ab(k))] in
private theorem isIso_of_presheafEvaluation {K L : DerivedCategory PST(k)} (f : K ⟶ L)
    (h : ∀ X : Cor k, IsIso ((presheafEvaluation k X).mapDerivedCategory.map f)) :
    IsIso f := by
  apply (DerivedCategory.isIso_iff _ f).2
  intro n
  let V := (PresheafWithTransfers.forget : PST(k) ⥤ (Cor k)ᵒᵖ ⥤ Ab(k))
  let q := (DerivedCategory.homologyFunctor PST(k) n).map f
  let : V.ReflectsIsomorphisms :=
    (additiveFunctor (Cor k)ᵒᵖ Ab(k)).fullyFaithfulι.reflectsIsomorphisms
  let : IsIso (V.map q) := (NatTrans.isIso_iff_isIso_app (V.map q)).2 (fun X =>
    ((presheafEvaluation k X.unop).isIso_mapDerivedCategory_map_iff f).1 (h X.unop) n)
  exact isIso_of_reflects_iso q V

omit [HasDerivedCategory PST(k)] [HasDerivedCategory NST(k)]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology Base(k)) Ab(k))] in
private def transferEvaluationUnderlyingIso (X : SmoothSite Base(k)) :
    transferEvaluationFunctor k X ≅ U(k) ⋙ presheafEvaluation k (Cor.mk X) :=
  NatIso.ofComponents (fun I => (transferSectionsEquiv k (Cor.mk X) I).toAddCommGrpIso)
    (fun f => by
      ext a
      exact transferSectionsEquiv_comp k (Cor.mk X) a f)

private theorem isIso_parameterForgetDerivedUnit (I : CochainComplex NST(k) ℤ)
    (hI : ∀ i, Injective (I.X i)) :
    IsIso ((forgetDerivedUnit k).app (((B(e)).mapHomologicalComplex c).obj I)) := by
  let J := ((B(e)).mapHomologicalComplex c).obj I
  apply isIso_of_presheafEvaluation
  intro X
  let E := presheafEvaluation k X
  let V := E.mapDerivedCategory
  let α := transferEvaluationDerivedUnit k X.toSmoothSite
  let R := forgetDerivedFunctor k ⋙ V
  let β : forgetComplexToDerived k ⋙ V ⟶ Qs(k) ⋙ R :=
    Functor.whiskerRight (forgetDerivedUnit k) V ≫
      (Functor.associator Qs(k) (forgetDerivedFunctor k) V).hom
  let δ := mapDerivedCategorySourceIsoQ U(k) E ≪≫ Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex (transferEvaluationUnderlyingIso (k := k) X.toSmoothSite).symm c)
    (DerivedCategory.Q (C := Ab(k)))
  have hβ (K : CochainComplex NST(k) ℤ) : β.app K = V.map ((forgetDerivedUnit k).app K) := by
    change V.map ((forgetDerivedUnit k).app K) ≫ 𝟙 _ = _
    exact Category.comp_id _
  let : R.IsRightDerivedFunctor β W(k) := by
    let hU : InvertsQuasiIsoOfIsKInjective (forgetComplexToDerived k) :=
      invertsQuasiIso_mapHomologicalComplex_comp_Q U(k)
    apply (isRightDerivedFunctor_iff_isIso_app_of_isKInjective Qs(k) R β
      (invertsQuasiIsoOfIsKInjective_comp hU V)).2
    intro K hK
    let : IsIso ((forgetDerivedUnit k).app K) := isIso_app_of_isKInjective Qs(k)
      (forgetDerivedFunctor k) (forgetDerivedUnit k) hU K hK
    rw [hβ]
    infer_instance
  let H := transferEvaluationDerivedFunctor k X.toSmoothSite
  let γ := Functor.rightDerivedNatIso R H β α W(k) δ
  have h : V.map ((forgetDerivedUnit k).app J) ≫ γ.hom.app ((Qs(k)).obj J) =
      δ.hom.app J ≫ α.app J := by
    exact (congrArg (· ≫ γ.hom.app ((Qs(k)).obj J)) (hβ J).symm).trans
      (Functor.rightDerivedNatTrans_app R H β α W(k) δ.hom J)
  let : IsIso (α.app J) := isIso_parameterEvaluationDerivedUnit e X.toSmoothSite I hI
  let : IsIso (V.map ((forgetDerivedUnit k).app J) ≫ γ.hom.app ((Qs(k)).obj J)) :=
    h.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_right _ (γ.hom.app ((Qs(k)).obj J))

private instance parameterForgetComposition_isRightDerived :
    (parameterSectionsDerived e ⋙ forgetDerivedFunctor k).IsRightDerivedFunctor
      (parameterForgetCompositionUnit e) W(k) := by
  let G := (B(e) ⋙ U(k)).mapHomologicalComplex c ⋙ Qp(k)
  let R := parameterSectionsDerived e ⋙ forgetDerivedFunctor k
  let η := parameterForgetCompositionUnit e
  let hG : InvertsQuasiIsoOfIsKInjective G :=
    invertsQuasiIso_mapHomologicalComplex_comp_Q (B(e) ⋙ U(k))
  apply (isRightDerivedFunctor_iff_isIso_app_of_isKInjective Qs(k) R η hG).2
  intro K hK
  let I := (Stacks.Injectives.kInjectiveResolutionFunctor NST(k)).obj K
  let i := (Stacks.Injectives.kInjectiveResolutionInclusion NST(k)).app K
  have hI : I.IsKInjective := inferInstance
  have hi : QuasiIso i := inferInstance
  let : IsIso (G.map i) := hG i hK hI hi
  let : IsIso ((Qs(k)).map i) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hi
  let : IsIso ((Qs(k) ⋙ R).map i) := inferInstanceAs (IsIso (R.map ((Qs(k)).map i)))
  have hη : IsIso (η.app I) := by
    let : IsIso ((forgetDerivedUnit k).app (((B(e)).mapHomologicalComplex c).obj I)) :=
      isIso_parameterForgetDerivedUnit e I (fun j => inferInstance)
    let : IsIso ((parameterSectionsDerivedUnit e).app I) :=
      isIso_app_of_isKInjective Qs(k) _ _ (invertsQuasiIso_mapHomologicalComplex_comp_Q (B(e))) I hI
    change IsIso ((forgetDerivedUnit k).app (((B(e)).mapHomologicalComplex c).obj I) ≫
      (forgetDerivedFunctor k).map ((parameterSectionsDerivedUnit e).app I))
    infer_instance
  have : IsIso (η.app K ≫ (Qs(k) ⋙ R).map i) :=
    (η.naturality i) ▸ IsIso.comp_isIso' (inferInstance : IsIso (G.map i)) hη
  exact IsIso.of_isIso_comp_right _ ((Qs(k) ⋙ R).map i)

/-- Right deriving the original sheaf parameter sections and then forgetting
agrees with exact presheaf reindexing of the derived underlying coefficient. -/
@[no_expose]
def parameterSectionsDerivedForgetIso :
    parameterSectionsDerived e ⋙ forgetDerivedFunctor k ≅
      forgetDerivedFunctor k ⋙ (P(F)).mapDerivedCategory :=
  Functor.rightDerivedNatIso _ _ (parameterForgetCompositionUnit e)
    (reindexedForgetUnit (k := k) (F := F)) W(k) (Iso.refl _)

end AlgebraicGeometry.SheafWithTransfers
