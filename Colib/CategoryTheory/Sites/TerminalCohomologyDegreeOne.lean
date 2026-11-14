/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.TerminalCohomologyDegreeZero

/-! # Original terminal degree-one boundaries evaluate source sections -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open Stacks.Cohomology.FreeYonedaUnivLE
universe w w' u
private lemma mkZero_comp_hom {A : Type*} [Category* A] [Abelian A]
    [HasExt.{w} A] [HasDerivedCategory.{w'} A] {Z G H : A}
    (f : Z ⟶ G) (δ : Ext.{w} G H 1) :
    ((Ext.mk₀ f).comp δ (zero_add 1)).hom =
      (DerivedCategory.singleFunctor A 0).map f ≫ δ.hom := by
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp]

namespace Stacks.Cohomology.FreeYonedaUnivLE
universe t v uC
variable {C : Type uC} [Category.{v} C]
variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max v t}]
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]
variable [HasDerivedCategory.{w'} (Sheaf J AddCommGrpCat.{max v t})]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- A native degree-one terminal boundary evaluates the original source section. -/
lemma terminalDerivedHomAddEquivH_zero_comp {F G : Sheaf J AddCommGrpCat.{max v t}}
    (U : C) (hU : IsTerminal U) (f : (freeYoneda.{t} J).obj U ⟶ F)
    (e : Ext.{w} F G 1) :
    terminalDerivedHomAddEquivH.{w, w', t} J G U hU 1
      ((DerivedCategory.singleFunctor _ 0).map f ≫ e.hom) =
      ((Sheaf.H.equiv₀ F hU).symm (sectionsEquiv.{t} U F f)).comp e (zero_add 1) := by
  rw [← mkZero_comp_hom f e]
  change terminalCohomologyAddEquiv.{w, t} J G U hU 1
    (Ext.homAddEquiv.symm (Ext.homAddEquiv ((Ext.mk₀ f).comp e (zero_add 1)))) = _
  rw [AddEquiv.symm_apply_apply, terminalCohomologyAddEquiv_comp.{w, t}]
  congr 1
  apply (Sheaf.H.equiv₀ F hU).injective
  rw [terminalCohomologyAddEquiv_zero.{w, t}, AddEquiv.apply_symm_apply]

end Stacks.Cohomology.FreeYonedaUnivLE

