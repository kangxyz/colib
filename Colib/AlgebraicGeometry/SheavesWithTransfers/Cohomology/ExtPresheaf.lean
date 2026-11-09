/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Representable
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-! # Genuine signed correspondence precomposition on transfer Ext -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite
universe w u
namespace AlgebraicGeometry.SheafWithTransfers
variable (k : Type u) [Field k] [HasExt.{w} (SheafWithTransfers.{u + 1} k)]
  (F : SheafWithTransfers.{u + 1} k) (n : ℕ)

/-- Precomposition by genuine signed correspondences on the actual transfer Ext source. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Cohomology/Ext/Presheaf.lean:23-25"
  "adaptation" "Actual extFunctor precomposition with signed correspondences"]
def transferExtPresheaf : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  (transferRepresentable k).op ⋙ extFunctor n ⋙
    (evaluation (SheafWithTransfers.{u + 1} k) AddCommGrpCat.{w}).obj F

instance transferExtPresheaf_additive : (transferExtPresheaf k F n).Additive := by
  dsimp only [transferExtPresheaf]
  infer_instance

/-- Coefficient morphisms commute with every signed-correspondence restriction. -/
def transferExtCoefficientMap {F G : SheafWithTransfers.{u + 1} k} (a : F ⟶ G) :
    transferExtPresheaf k F n ⟶ transferExtPresheaf k G n where
  app X := (extFunctorObj ((transferRepresentable k).obj X.unop) n).map a
  naturality {_X _Y} f :=
    (((extFunctor.{w} n).map ((transferRepresentable k).map f.unop).op).naturality a).symm

attribute [colib_tag "COL-0383"]
  transferExtPresheaf
  transferExtCoefficientMap

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean:421-451"
  "adaptation" "Native Ext precomposed with sheafified signed representables"]
  transferExtPresheaf

end AlgebraicGeometry.SheafWithTransfers
