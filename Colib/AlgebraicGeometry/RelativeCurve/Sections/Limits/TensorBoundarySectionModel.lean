/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.Invertible.PullbackTensorFrameComparison
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.BoundarySectionFrames

/-! # Original numerator normalization through the same tensor model

The specified original root and auxiliary model isomorphisms determine the actual
tensor model and the normalized boundary product frame. Their original numerator
has the same full-boundary scalar under this model, not an assumed matching frame.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
open Stacks.SheafOfModules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem tensor_model_frame_aux {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) {A B C' : C} {U : D} (E : A ≅ B) (T : C' ≅ B)
    (e : G.obj A ≅ U) (q : G.obj B ≅ U) (hq : (G.mapIso E).symm ≪≫ e = q) :
    G.mapIso (E ≪≫ T.symm).symm ≪≫ e = G.mapIso T ≪≫ q := by
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Functor.mapIso_trans, Iso.trans_assoc,
    Functor.mapIso_symm]
  rw [hq]

/-- The normalized product frame is exactly transport of the original product
frame through the tensor of the specified original root and auxiliary models. -/
theorem tensorBoundaryFrame_originalModel {B X Y : Scheme.{u}}
    (i : B ⟶ X) (p : X ⟶ Y) (L Q : Y.Modules) (M N : X.Modules)
    (E : M ≅ (pullback p).obj L) (F : N ≅ (pullback p).obj Q)
    (eM : (pullback i).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf) :
    (pullback i).mapIso
        (tensorProductIso X.sheaf.obj X.ringCatSheaf.property E F ≪≫
          (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L Q).symm).symm ≪≫
        pullbackTensorFrame i M N eM eN =
      (pullback i).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L Q) ≪≫
        pullbackTensorFrame i ((pullback p).obj L) ((pullback p).obj Q)
          (((pullback i).mapIso E).symm ≪≫ eM) (((pullback i).mapIso F).symm ≪≫ eN) := by
  exact tensor_model_frame_aux (pullback i)
    (tensorProductIso X.sheaf.obj X.ringCatSheaf.property E F)
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L Q)
    (pullbackTensorFrame i M N eM eN) _ (pullbackTensorFrame_naturality i E F eM eN)

/-- Actual recovery of the original numerator under the canonical tensor model
preserves its specified full-boundary scalar with both original factor frames. -/
theorem tensorBoundaryFrame_originalSection {B X Y : Scheme.{u}}
    (i : B ⟶ X) (p : X ⟶ Y) (L Q : Y.Modules) (M N : X.Modules)
    (E : M ≅ (pullback p).obj L) (F : N ≅ (pullback p).obj Q)
    (eM : (pullback i).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N, ⊤))
    (t : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj L).obj Q, ⊤))
    (ht : Hom.app
      (tensorProductIso X.sheaf.obj X.ringCatSheaf.property E F ≪≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L Q).symm).hom ⊤ a =
      pullbackGlobalSections p _ t) :
    Hom.app
      ((pullback i).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L Q) ≪≫
        pullbackTensorFrame i ((pullback p).obj L) ((pullback p).obj Q)
          (((pullback i).mapIso E).symm ≪≫ eM)
          (((pullback i).mapIso F).symm ≪≫ eN)).hom ⊤
      (pullbackGlobalSections i _ (pullbackGlobalSections p _ t)) =
    Hom.app (pullbackTensorFrame i M N eM eN).hom ⊤ (pullbackGlobalSections i _ a) := by
  rw [← tensorBoundaryFrame_originalModel i p L Q M N E F eM eN]
  exact originalBoundaryFrame_section_model i _ (pullbackTensorFrame i M N eM eN) a _ ht

end AlgebraicGeometry.Scheme.Modules
