/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.AuxiliaryNumeratorDescentEquation

/-! # Actual original numerator equation without a stage root frame -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
namespace AlgebraicGeometry.Scheme.Modules

example {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D)
    (w : f ≫ g = h ≫ k) (L N : D.Modules)
    (eN : (pullback g).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (eL : (pullback h).obj ((pullback k).obj L) ≅ SheafOfModules.unit A.ringCatSheaf)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor D.sheaf).obj L).obj N, ⊤)) :
    (pullback f).map (auxiliaryBoundaryNumerator g L N eN a) ≫
        (framePullbackIso f g h k w L eL).hom =
      (pullback f).map (unitHomEquivTop (SheafOfModules.unit B.ringCatSheaf)
        (1 : Γ(B, ⊤))) ↔
    Hom.app
      ((pullback h).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso k L N) ≪≫
        pullbackTensorFrame h ((pullback k).obj L) ((pullback k).obj N) eL
          (pullbackBoundaryTrivialization f g h k w N eN)).hom ⊤
      (pullbackGlobalSections h _ (pullbackGlobalSections k _ a)) = (1 : Γ(A, ⊤)) := auxiliaryBoundaryNumerator_pullback_one_iff f g h k w L N eN eL a

#print axioms auxiliaryBoundaryNumerator_pullback_one_iff

example {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D)
    (w : f ≫ g = h ≫ k) (L N : D.Modules) (M P : C.Modules)
    (E : M ≅ (pullback k).obj L) (F : P ≅ (pullback k).obj N)
    (eM : (pullback h).obj M ≅ SheafOfModules.unit A.ringCatSheaf)
    (eP : (pullback h).obj P ≅ SheafOfModules.unit A.ringCatSheaf)
    (eN : (pullback g).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (hN : pullbackBoundaryTrivialization f g h k w N eN =
      ((pullback h).mapIso F).symm ≪≫ eP)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor C.sheaf).obj M).obj P, ⊤))
    (t : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor D.sheaf).obj L).obj N, ⊤))
    (ht : Hom.app
      (Stacks.SheafOfModules.Invertible.tensorProductIso C.sheaf.obj C.ringCatSheaf.property E F ≪≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso k L N).symm).hom ⊤ a =
      pullbackGlobalSections k _ t) :
    (pullback f).map (auxiliaryBoundaryNumerator g L N eN t) ≫
        (framePullbackIso f g h k w L (((pullback h).mapIso E).symm ≪≫ eM)).hom =
      (pullback f).map (unitHomEquivTop (SheafOfModules.unit B.ringCatSheaf)
        (1 : Γ(B, ⊤))) ↔
    Hom.app (pullbackTensorFrame h M P eM eP).hom ⊤
      (pullbackGlobalSections h _ a) = (1 : Γ(A, ⊤)) := auxiliaryBoundaryNumerator_original_one_iff f g h k w L N M P E F eM eP eN hN a t ht

#print axioms auxiliaryBoundaryNumerator_original_one_iff

end AlgebraicGeometry.Scheme.Modules
