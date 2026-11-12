/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.Invertible.PullbackTensorAuxiliaryFrameComparison
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.TensorBoundarySectionModel

/-! # The actual numerator supplies the finite root-frame descent equation

Only the auxiliary boundary frame is given at the intermediate stage. The root
frame remains on the limit. The original boundary square and literal numerator
produce the native finite linear equation without assuming a stage root frame.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem contraction_frame_aux {C : Type*} [Category C] {A B D E F U : C}
    (a : A ≅ B) (b : B ≅ D) (c : A ≅ E) (d : E ≅ F) (e : F ≅ D)
    (r : D ≅ U) (s : F ≅ U) (h : a ≪≫ b = c ≪≫ d ≪≫ e)
    (hr : e ≪≫ r = s) : a ≪≫ b ≪≫ r = c ≪≫ d ≪≫ s := by
  simpa only [Iso.trans_assoc, hr] using congrArg (fun z => z ≪≫ r) h

/-- The actual contracted numerator gives precisely the normalized finite linear
equation for the specified limit root frame. No root frame at the stage is used. -/
theorem auxiliaryBoundaryNumerator_pullback_one_iff {A B C D : Scheme.{u}}
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
      (pullbackGlobalSections h _ (pullbackGlobalSections k _ a)) = (1 : Γ(A, ⊤)) := by
  let T := ((Stacks.SheafOfModules.Tensor.sheafTensor D.sheaf).obj L).obj N
  let v := pullbackGlobalSections g T a
  let c := pullbackTensorAuxiliaryFrame g L N eN
  have hs : unitHomEquivTop _ v ≫ c.hom = unitHomEquivTop _ (Hom.app c.hom ⊤ v) :=
    (unitHomEquivTop_comp_eq_iff _ _ _).mpr rfl
  change (pullback f).map (unitHomEquivTop _ v ≫ c.hom) ≫ _ = _ ↔ _
  rw [hs]
  refine (framePullbackIso_section_one_iff f g h k w L eL (Hom.app c.hom ⊤ v)).trans ?_
  have hc := contraction_frame_aux ((pullback f).mapIso c)
    (pullbackSquareIso f g h k w L) (pullbackSquareIso f g h k w T)
    ((pullback h).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso k L N))
    (pullbackTensorAuxiliaryFrame h ((pullback k).obj L) ((pullback k).obj N)
      (pullbackBoundaryTrivialization f g h k w N eN)) eL
    (pullbackTensorFrame h ((pullback k).obj L) ((pullback k).obj N) eL
      (pullbackBoundaryTrivialization f g h k w N eN))
    (pullbackTensorAuxiliaryFrame_square f g h k w L N eN)
    (pullbackTensorAuxiliaryFrame_trans h ((pullback k).obj L) ((pullback k).obj N) eL
      (pullbackBoundaryTrivialization f g h k w N eN))
  have H := congrArg (fun e => Hom.app (Iso.hom e) ⊤ (pullbackGlobalSections f _ v)) hc
  have hn := Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality
    f c.hom v
  have hp := pullbackSquareIso_pullbackGlobalSections f g h k w T a
  have hv : Hom.app (pullbackSquareIso f g h k w L ≪≫ eL).hom ⊤
      (pullbackGlobalSections f _ (Hom.app c.hom ⊤ v)) =
    Hom.app
      ((pullback h).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso k L N) ≪≫
        pullbackTensorFrame h ((pullback k).obj L) ((pullback k).obj N) eL
          (pullbackBoundaryTrivialization f g h k w N eN)).hom ⊤
      (pullbackGlobalSections h _ (pullbackGlobalSections k _ a)) := by
    exact (congrArg (Hom.app (pullbackSquareIso f g h k w L ≪≫ eL).hom ⊤) hn).trans
      (H.trans (congrArg (Hom.app
        ((pullback h).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso k L N) ≪≫
          pullbackTensorFrame h ((pullback k).obj L) ((pullback k).obj N) eL
            (pullbackBoundaryTrivialization f g h k w N eN)).hom ⊤) hp))
  exact Iff.of_eq (congrArg (fun z => z = (1 : Γ(A, ⊤))) hv)

/-- Recovery of the actual auxiliary frame and numerator supplies exactly the
finite equation for the original root frame. Its right side is the original
full-boundary scalar, retaining the same root, auxiliary model, and numerator. -/
theorem auxiliaryBoundaryNumerator_original_one_iff {A B C D : Scheme.{u}}
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
      (pullbackGlobalSections h _ a) = (1 : Γ(A, ⊤)) := by
  refine (auxiliaryBoundaryNumerator_pullback_one_iff f g h k w L N eN
    (((pullback h).mapIso E).symm ≪≫ eM) t).trans ?_
  rw [hN]
  exact Iff.of_eq (congrArg (fun z => z = (1 : Γ(A, ⊤)))
    (tensorBoundaryFrame_originalSection h k L N M P E F eM eP a t ht))

end AlgebraicGeometry.Scheme.Modules
