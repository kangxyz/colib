/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.TorusEvaluationAcyclic
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.EvaluationFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.TermwiseAcyclicComputesRightDerived
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

/-!
# Total derived evaluation on the actual torus product

Evaluation at a smooth transfer representable has finite cohomological
dimension. After applying torus sections, the terms of the functorial
K-injective resolution are evaluation-acyclic. The original represented
evaluation isomorphism therefore identifies the two total derived functors.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe w w' u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme
open Stacks.Injectives.KInjectiveResolution

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

local notation "S" => Spec (CommRingCat.of k)
local notation "G" => SmoothSite.multiplicativeGroupObject S

variable [HasExt.{u + 1}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

private theorem isIso_evaluationDerivedUnit_app_torus_of_injective
    (X : SmoothSite S) (I : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ)
    (hI : ∀ i, Injective (I.X i)) :
    IsIso ((transferEvaluationDerivedUnit k X).app
      (((torusSectionsFunctor k).mapHomologicalComplex (.up ℤ)).obj I)) := by
  obtain ⟨d, hd⟩ := exists_transferRepresentable_hasProjectiveDimensionLE k X
  let : HasProjectiveDimensionLE ((transferRepresentable k).obj (Cor.mk X)) d := hd
  apply Functor.isIso_app_of_rightAcyclic_of_isZero_rightDerived (transferEvaluationFunctor k X)
    (d + 1) (isZero_rightDerived_transferEvaluation_of_hasProjectiveDimensionLE k X d)
    (transferEvaluationDerivedFunctor k X)
  intro i p hp
  let : Injective (I.X i) := hI i
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  exact isZero_rightDerived_transferEvaluation_torusSections_injective k X (I.X i) n

/-- The actual comparison unit from original cochain evaluation on
the reindexed complex to the composite of the two total derived functors. -/
@[no_expose]
def torusSectionsEvaluationDerivedUnit (X : SmoothSite S) :
    (torusSectionsFunctor k ⋙ transferEvaluationFunctor k X).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙
        (torusSectionsDerivedFunctor k ⋙ transferEvaluationDerivedFunctor k X) :=
  let B := torusSectionsFunctor k
  let E := transferEvaluationDerivedFunctor k X
  Functor.whiskerLeft (B.mapHomologicalComplex (.up ℤ)) (transferEvaluationDerivedUnit k X) ≫
    Functor.whiskerRight (torusSectionsDerivedUnit k) E

omit [HasExt.{u + 1}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
/-- The evaluation composition uses both original derived units on a cochain complex. -/
theorem torusSectionsEvaluationDerivedUnit_app (X : SmoothSite S)
    (K : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ) :
    (torusSectionsEvaluationDerivedUnit k X).app K =
      (transferEvaluationDerivedUnit k X).app
        (((torusSectionsFunctor k).mapHomologicalComplex (.up ℤ)).obj K) ≫
      (transferEvaluationDerivedFunctor k X).map ((torusSectionsDerivedUnit k).app K) := by
  unfold torusSectionsEvaluationDerivedUnit
  rfl

private theorem isIso_torusSectionsEvaluationDerivedUnit_app_resolution (X : SmoothSite S)
    (K : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ) :
    IsIso ((torusSectionsEvaluationDerivedUnit k X).app
      ((Stacks.Injectives.kInjectiveResolutionFunctor _).obj K)) := by
  let I := (Stacks.Injectives.kInjectiveResolutionFunctor _).obj K
  have hI : I.IsKInjective := inferInstanceAs
    (((Stacks.Injectives.kInjectiveResolutionFunctor _).obj K).IsKInjective)
  let : IsIso ((torusSectionsDerivedUnit k).app I) :=
    isIso_app_of_isKInjective DerivedCategory.Q (torusSectionsDerivedFunctor k)
      (torusSectionsDerivedUnit k)
      (invertsQuasiIso_mapHomologicalComplex_comp_Q (torusSectionsFunctor k)) I hI
  let : IsIso ((transferEvaluationDerivedUnit k X).app
      (((torusSectionsFunctor k).mapHomologicalComplex (.up ℤ)).obj I)) :=
    isIso_evaluationDerivedUnit_app_torus_of_injective k X I
      (fun i => inferInstanceAs
        (Injective (((Stacks.Injectives.kInjectiveResolutionFunctor _).obj K).X i)))
  change IsIso ((transferEvaluationDerivedUnit k X).app
      (((torusSectionsFunctor k).mapHomologicalComplex (.up ℤ)).obj I) ≫
    (transferEvaluationDerivedFunctor k X).map ((torusSectionsDerivedUnit k).app I))
  infer_instance

instance (X : SmoothSite S) :
    (torusSectionsDerivedFunctor k ⋙
      transferEvaluationDerivedFunctor k X).IsRightDerivedFunctor
      (torusSectionsEvaluationDerivedUnit k X)
      (HomologicalComplex.quasiIso (SheafWithTransfers.{u + 1} k) (.up ℤ)) := by
  apply (isRightDerivedFunctor_iff_isIso_app_of_isKInjective DerivedCategory.Q _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q
      (torusSectionsFunctor k ⋙ transferEvaluationFunctor k X))).2
  intro K hK
  let ι := (Stacks.Injectives.kInjectiveResolutionInclusion _).app K
  let I := (Stacks.Injectives.kInjectiveResolutionFunctor _).obj K
  let hι : QuasiIso ι := inferInstanceAs
    (QuasiIso ((Stacks.Injectives.kInjectiveResolutionInclusion _).app K))
  let hI : I.IsKInjective := inferInstanceAs
    (((Stacks.Injectives.kInjectiveResolutionFunctor _).obj K).IsKInjective)
  let θ := torusSectionsEvaluationDerivedUnit k X
  let q : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ ⥤
      DerivedCategory (SheafWithTransfers.{u + 1} k) := DerivedCategory.Q
  let Q : CochainComplex AddCommGrpCat.{u + 1} ℤ ⥤
      DerivedCategory AddCommGrpCat.{u + 1} := DerivedCategory.Q
  let F := (torusSectionsFunctor k ⋙ transferEvaluationFunctor k X).mapHomologicalComplex
    (.up ℤ) ⋙ Q
  let V := torusSectionsDerivedFunctor k ⋙ transferEvaluationDerivedFunctor k X
  let R := q ⋙ V
  let : IsIso (F.map ι) :=
    invertsQuasiIso_mapHomologicalComplex_comp_Q
      (torusSectionsFunctor k ⋙ transferEvaluationFunctor k X) ι hK hI hι
  let : IsIso (q.map ι) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hι
  let : IsIso (R.map ι) := inferInstanceAs (IsIso (V.map (q.map ι)))
  let : IsIso (θ.app I) := isIso_torusSectionsEvaluationDerivedUnit_app_resolution k X K
  let : IsIso (θ.app K ≫ R.map ι) := by
    have h : F.map ι ≫ θ.app I = θ.app K ≫ R.map ι := θ.naturality ι
    exact h ▸ IsIso.comp_isIso' (inferInstance : IsIso (F.map ι))
      (inferInstance : IsIso (θ.app I))
  exact IsIso.of_isIso_comp_right _ (R.map ι)

/-- Derived evaluation of the actual torus reindexing is derived evaluation
at the original torus-product representable. -/
@[no_expose]
def torusSectionsEvaluationDerivedIso (X : SmoothSite S) :
    torusSectionsDerivedFunctor k ⋙ transferEvaluationDerivedFunctor k X ≅
      transferEvaluationDerivedFunctor k (SmoothSite.product X G) :=
  Functor.rightDerivedNatIso _ _ (torusSectionsEvaluationDerivedUnit k X)
    (transferEvaluationDerivedUnit k (SmoothSite.product X G))
    (HomologicalComplex.quasiIso _ (.up ℤ))
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (torusSectionsTransferEvaluationIso k X) (.up ℤ))
      DerivedCategory.Q)

end AlgebraicGeometry.SheafWithTransfers
