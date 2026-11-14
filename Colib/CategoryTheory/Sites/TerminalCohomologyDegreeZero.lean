/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.TerminalCohomologyBoundary

/-! # The original terminal-source comparison in degree zero -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
universe w t v u
namespace Stacks.Cohomology.FreeYonedaUnivLE
variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max v t}]
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

omit [HasExt (Sheaf J AddCommGrpCat.{max v t})] in
/-- The native inverse terminal-source presheaf iso sends one to the identity generator. -/
lemma freeYonedaTerminalIsoConstULiftInt_inv_one (U : C) (hU : IsTerminal U) :
    ((freeYonedaTerminalIsoConstULiftInt.{t} U hU).inv.app (op U)) (ULift.up (1 : ℤ)) =
      FreeAbelianGroup.of (ULift.up (𝟙 U)) := by
  have h (v : ULift.{t} (U ⟶ U)) : v = ULift.up (𝟙 U) := by
    apply ULift.ext
    exact hU.hom_ext _ _
  simp [freeYonedaTerminalIsoConstULiftInt, uliftYonedaTerminalIsoConstPUnit,
    TerminalCohomology.freeObjPUnitIsoULiftInt, FreeAbelianGroup.uniqueEquiv,
    AddEquiv.ulift, h]

/-- The actual terminal-source comparison in degree zero is the original section evaluation. -/
lemma terminalCohomologyAddEquiv_zero (F : Sheaf J AddCommGrpCat.{max v t})
    (U : C) (hU : IsTerminal U) (f : (freeYoneda.{t} J).obj U ⟶ F) :
    Sheaf.H.equiv₀ F hU (terminalCohomologyAddEquiv J F U hU 0 (Ext.mk₀ f)) =
      sectionsEquiv U F f := by
  change Sheaf.H.equiv₀ F hU
    ((Ext.mk₀ (freeYonedaTerminalIsoConstantSheaf J U hU).inv).comp
      (Ext.mk₀ f) (zero_add 0)) = _
  rw [Ext.mk₀_comp_mk₀]
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply, ← Ext.addEquiv₀_symm_apply,
    AddEquiv.apply_symm_apply]
  change (((sheafificationAdjunction J AddCommGrpCat.{max v t}).homEquiv _ F
      ((freeYonedaTerminalIsoConstantSheaf J U hU).inv ≫ f)).app (op U)) (ULift.up (1 : ℤ)) = _
  change (((sheafificationAdjunction J AddCommGrpCat.{max v t}).homEquiv _ F
      ((presheafToSheaf J AddCommGrpCat.{max v t}).map
        (freeYonedaTerminalIsoConstULiftInt U hU).inv ≫ f)).app (op U)) (ULift.up (1 : ℤ)) = _
  rw [(sheafificationAdjunction J AddCommGrpCat.{max v t}).homEquiv_naturality_left]
  change (((sheafificationAdjunction J AddCommGrpCat.{max v t}).homEquiv _ F f).app (op U))
    (((freeYonedaTerminalIsoConstULiftInt U hU).inv.app (op U)) (ULift.up (1 : ℤ))) = _
  rw [freeYonedaTerminalIsoConstULiftInt_inv_one]
  rfl

end Stacks.Cohomology.FreeYonedaUnivLE
