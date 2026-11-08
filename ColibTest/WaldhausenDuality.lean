/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.Waldhausen.Duality.SConstruction
import Colib.CategoryTheory.Waldhausen.Duality.InverseImageWeak
import Colib.CategoryTheory.Waldhausen.Approximation.Dual

/-! Regression checks for whole grid reversal, native maps and independent universes. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen Opposite SSet Topology
open scoped Simplicial Topology

universe u v u' v'

section Structural

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {Wd : Structure Cᵒᵖ} {V : Structure D} {Vd : Structure Dᵒᵖ}
  (hW : IsCompatibleDual W Wd) (hV : IsCompatibleDual V Vd) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hFd : IsExact Wd.cof Wd.weq Vd.cof Vd.weq F.op)

example (h : HasDualApproximationProperty W V Wd.cof.unop F) :
    HasApproximationProperty Wd Vd F.op := h.op hW hV

example [W.weq.HasTwoOutOfThreeProperty] : Wd.weq.HasTwoOutOfThreeProperty :=
  hW.dual_saturated

example : IsCompatibleDual (Structure.withInverseImageWeak hF)
    (Structure.withInverseImageWeak hFd) := hW.withInverseImageWeak hV hF hFd

example {A B : C} (f : A ⟶ B) :
    (Structure.withInverseImageWeak hF).weq f ↔ V.weq (F.map f) := Iff.rfl

end Structural

section Grids

variable {C : Type u} [Category.{v} C] {W : Structure C} {Wd : Structure Cᵒᵖ}
  (hW : IsCompatibleDual W Wd)

example {m n : SimplexCategory} (α : m ⟶ n) :
    gridMap α ⋙ DualSConstruction.reverseGrid n =
      DualSConstruction.reverseGrid m ⋙ (gridMap (SimplexCategory.rev.map α)).op :=
  DualSConstruction.reverseGrid_naturality α

example {m n : SimplexCategory} (α : m ⟶ n) (A : Grid n ⥤ C) :
    DualSConstruction.reverseOp (gridMap (SimplexCategory.rev.map α) ⋙ A) =
      gridMap α ⋙ DualSConstruction.reverseOp A :=
  DualSConstruction.reverseOp_precomp α A

example {n : SimplexCategory} (A : Grid n ⥤ C) :
    DualSConstruction.reverseUnop (DualSConstruction.reverseOp A) = A :=
  DualSConstruction.reverseUnop_reverseOp A

example {n : SimplexCategory} (A : Grid n ⥤ Cᵒᵖ) :
    DualSConstruction.reverseOp (DualSConstruction.reverseUnop A) = A :=
  DualSConstruction.reverseOp_reverseUnop A

example : (sSet W.cof W.weq).op ≅ sSet Wd.cof Wd.weq :=
  DualSConstruction.sSetIso hW

example : |sSet W.cof W.weq| ≃ₜ |sSet Wd.cof Wd.weq| :=
  DualSConstruction.realizationHomeomorph hW

variable {D : Type u} [Category.{v} D] {V : Structure D} {Vd : Structure Dᵒᵖ}
  (hV : IsCompatibleDual V Vd) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hFd : IsExact Wd.cof Wd.weq Vd.cof Vd.weq F.op)

example : SSet.opFunctor.map (sSetMap hF) ≫ (DualSConstruction.sSetIso hV).hom =
    (DualSConstruction.sSetIso hW).hom ≫ sSetMap hFd :=
  DualSConstruction.sSetIso_naturality hW hV hF hFd

example (hd : IsRealizationWeakEquivalence (sSetMap hFd)) :
    IsRealizationWeakEquivalence (sSetMap hF) :=
  DualSConstruction.sSetMap_weak_of_dual hW hV hF hFd hd

end Grids
