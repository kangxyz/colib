/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.FiniteDimension
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.TorusEvaluation
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived
import Colib.Algebra.Homology.DerivedCategory.Ext.RightDerived
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

/-! # Total derived evaluation of a smooth transfer representable -/

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

/-- Apply the original represented evaluation to each term before localizing. -/
abbrev transferEvaluationComplexToDerived (X : SmoothSite S) :
    CochainComplex (SheafWithTransfers.{u + 1} k) ℤ ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  (transferEvaluationFunctor k X).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

instance (X : SmoothSite S) : (transferEvaluationComplexToDerived k X).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (SheafWithTransfers.{u + 1} k) (.up ℤ)) :=
  hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (transferEvaluationFunctor k X)

/-- The total right-derived functor of the actual transfer evaluation. -/
@[no_expose]
def transferEvaluationDerivedFunctor (X : SmoothSite S) :
    DerivedCategory (SheafWithTransfers.{u + 1} k) ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  (transferEvaluationComplexToDerived k X).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafWithTransfers.{u + 1} k) (.up ℤ))

/-- The actual unit of total derived evaluation on cochain complexes. -/
@[no_expose]
def transferEvaluationDerivedUnit (X : SmoothSite S) :
    transferEvaluationComplexToDerived k X ⟶
      DerivedCategory.Q ⋙ transferEvaluationDerivedFunctor k X :=
  (transferEvaluationComplexToDerived k X).totalRightDerivedUnit DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafWithTransfers.{u + 1} k) (.up ℤ))

instance (X : SmoothSite S) :
    (transferEvaluationDerivedFunctor k X).IsRightDerivedFunctor
      (transferEvaluationDerivedUnit k X)
      (HomologicalComplex.quasiIso (SheafWithTransfers.{u + 1} k) (.up ℤ)) := by
  dsimp only [transferEvaluationDerivedFunctor, transferEvaluationDerivedUnit]
  infer_instance

omit [HasDerivedCategory (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory AddCommGrpCat.{u + 1}] in
/-- Finite projective dimension of the actual smooth representable gives
one uniform zero degree for its derived evaluation. -/
theorem isZero_rightDerived_transferEvaluation_of_hasProjectiveDimensionLE
    (X : SmoothSite S) (d : ℕ)
    [HasProjectiveDimensionLE ((transferRepresentable k).obj (Cor.mk X)) d]
    (F : SheafWithTransfers.{u + 1} k) :
    IsZero (((transferEvaluationFunctor k X).rightDerived (d + 1)).obj F) := by
  let Z := (transferRepresentable k).obj (Cor.mk X)
  let : HasExt.{u + 1} (SheafWithTransfers.{u + 1} k) := hasExt_of_enoughInjectives _
  let e := (injectiveResolution F).extRightDerivedAddEquiv Z (d + 1)
  let h : Subsingleton (Ext.{u + 1} Z F (d + 1)) :=
    HasProjectiveDimensionLT.subsingleton Z (d + 1) (d + 1) le_rfl F
  exact AddCommGrpCat.isZero_iff_subsingleton.2
    ⟨fun a b => e.symm.injective (h.elim _ _)⟩

end AlgebraicGeometry.SheafWithTransfers
