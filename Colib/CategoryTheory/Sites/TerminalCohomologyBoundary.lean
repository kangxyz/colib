/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.TerminalCohomologyUnivLE
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! # Terminal-source comparison preserves actual extension boundaries -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w w' t v u

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max v t}]
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Terminal-source comparison commutes with composition by any actual extension class. -/
lemma terminalCohomologyAddEquiv_comp {F G : Sheaf J AddCommGrpCat.{max v t}}
    (U : C) (hU : IsTerminal U) (p q r : ℕ) (h : p + q = r)
    (x : (cohomologyPresheaf.{w, t} F p).obj (op U)) (e : Ext.{w} F G q) :
    terminalCohomologyAddEquiv J G U hU r (x.comp e h) =
      (terminalCohomologyAddEquiv J F U hU p x).comp e h := by
  change (Ext.mk₀ (freeYonedaTerminalIsoConstantSheaf J U hU).inv).comp
      (x.comp e h) (zero_add r) =
    ((Ext.mk₀ (freeYonedaTerminalIsoConstantSheaf J U hU).inv).comp
      x (zero_add p)).comp e h
  symm
  exact Ext.comp_assoc _ _ _ (zero_add p) h (by omega)

variable [HasDerivedCategory.{w'} (Sheaf J AddCommGrpCat.{max v t})]

/-- The actual derived-Hom to ordinary-H comparison preserves extension boundaries. -/
lemma terminalDerivedHomAddEquivH_comp {F G : Sheaf J AddCommGrpCat.{max v t}}
    (U : C) (hU : IsTerminal U) (p q r : ℕ) (h : p + q = r)
    (x : (DerivedCategory.singleFunctor _ 0).obj ((freeYoneda.{t} J).obj U) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj F)⟦(p : ℤ)⟧)
    (e : Ext.{w} F G q) :
    terminalDerivedHomAddEquivH J G U hU r
      (((Ext.homAddEquiv.symm x).comp e h).hom) =
      (terminalDerivedHomAddEquivH J F U hU p x).comp e h := by
  change terminalDerivedHomAddEquivH J G U hU r
    (Ext.homAddEquiv ((Ext.homAddEquiv.symm x).comp e h)) = _
  simp only [terminalDerivedHomAddEquivH, AddEquiv.trans_apply,
    AddEquiv.symm_apply_apply]
  change (Ext.mk₀ (freeYonedaTerminalIsoConstantSheaf J U hU).inv).comp
      ((Ext.homAddEquiv.symm x).comp e h) (zero_add r) =
    ((Ext.mk₀ (freeYonedaTerminalIsoConstantSheaf J U hU).inv).comp
      (Ext.homAddEquiv.symm x) (zero_add p)).comp e h
  symm
  exact Ext.comp_assoc _ _ _ (zero_add p) h (by omega)

end Stacks.Cohomology.FreeYonedaUnivLE
