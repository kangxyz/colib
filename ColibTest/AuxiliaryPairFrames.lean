/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.AuxiliaryPairFrames

/-! # Original auxiliary frame contraction and numerator linear-equation regressions -/
noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
universe u
example {X B : Scheme.{u}} (i : B ⟶ X)
    (L N : X.Modules)
    (e : (pullback i).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf) :
    pullbackTensorAuxiliaryFrame i L N eN ≪≫ e = pullbackTensorFrame i L N e eN :=
  pullbackTensorAuxiliaryFrame_trans i L N e eN

example {X B : Scheme.{u}} (i : B ⟶ X)
    (L N : X.Modules)
    (e : (pullback i).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj L).obj N, ⊤)) :
    auxiliaryBoundaryNumerator i L N eN a ≫ e.hom =
      unitHomEquivTop (SheafOfModules.unit B.ringCatSheaf) (1 : Γ(B, ⊤)) ↔
    Hom.app (pullbackTensorFrame i L N e eN).hom ⊤
      (pullbackGlobalSections i _ a) = (1 : Γ(B, ⊤)) :=
  auxiliaryBoundaryNumerator_frame_eq_iff i L N e eN a

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackTensorAuxiliaryFrame_trans
#print axioms AlgebraicGeometry.Scheme.Modules.unitHomEquivTop_comp_eq_iff
#print axioms AlgebraicGeometry.Scheme.Modules.auxiliaryBoundaryNumerator_frame_eq_iff
