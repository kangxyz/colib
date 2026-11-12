/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.TensorSectionModelTransport
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.ModelRefinementComposition

/-! # Actual numerator refinement with the direct original root model

A section descended in the iterated tensor pullback is transported into the direct
root pullback tensored with the same refined auxiliary module. The original root
model and original numerator are retained by the native canonical cocycle.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.SheafOfModules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem iso_map_refl_right {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A : D} {B : C} (E : A ≅ F.obj B) : E ≪≫ F.mapIso (Iso.refl B) = E := by
  simp

/-- Refine the actual numerator and auxiliary module while keeping the root as
the direct pullback from its original stage. No new root or section is chosen. -/
theorem directRootTensorSection_refinement {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (p : W ⟶ Y) (r : X ⟶ Z) (q : W ⟶ Z)
    (hfg : f ≫ g = p) (hgh : g ≫ h = r) (hph : p ≫ h = q) (hfr : f ≫ r = q)
    (L : Z.Modules) (N : Y.Modules) (M A : W.Modules)
    (E : M ≅ (pullback q).obj L) (F : A ≅ (pullback p).obj N)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf).obj M).obj A, ⊤))
    (t : Γ((pullback g).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj ((pullback h).obj L)).obj N), ⊤))
    (ht : Hom.app
      (refinedSectionModelIso f g p hfg
        (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj ((pullback h).obj L)).obj N)
        (tensorProductIso W.sheaf.obj W.ringCatSheaf.property
          (refinedSectionModelIso p h q hph L E) F ≪≫
          (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p ((pullback h).obj L) N).symm)
      ).hom ⊤ a = pullbackGlobalSections f _ t) :
    Hom.app
      (tensorProductIso W.sheaf.obj W.ringCatSheaf.property
        (refinedSectionModelIso f r q hfr L E) (refinedSectionModelIso f g p hfg N F) ≪≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
          ((pullback r).obj L) ((pullback g).obj N)).symm).hom ⊤ a =
      pullbackGlobalSections f _
        (Hom.app
          (tensorProductIso X.sheaf.obj X.ringCatSheaf.property
            (canIso g h r hgh L) (Iso.refl ((pullback g).obj N))).hom ⊤
          (Hom.app (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g
            ((pullback h).obj L) N).hom ⊤ t)) := by
  let ER := refinedSectionModelIso f g p hfg ((pullback h).obj L)
    (refinedSectionModelIso p h q hph L E)
  let EN := refinedSectionModelIso f g p hfg N F
  have hs := tensorModelIso_refinement_section f g p hfg ((pullback h).obj L) N M A
    (refinedSectionModelIso p h q hph L E) F a t ht
  have H := tensorSectionModelIso_transport_section f ER EN (canIso g h r hgh L)
    (Iso.refl ((pullback g).obj N)) a
    (Hom.app (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g
      ((pullback h).obj L) N).hom ⊤ t) hs
  have hr := refinedSectionModelIso_comp f g h p r q hfg hgh hph hfr L E
  have hn := iso_map_refl_right (pullback f) EN
  exact (congrArg₂ (fun x y => Hom.app
    (tensorProductIso W.sheaf.obj W.ringCatSheaf.property x y ≪≫
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
        ((pullback r).obj L) ((pullback g).obj N)).symm).hom ⊤ a) hr hn).symm.trans H

end AlgebraicGeometry.Scheme.Modules
