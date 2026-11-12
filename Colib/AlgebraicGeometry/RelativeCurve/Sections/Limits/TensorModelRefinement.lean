/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.AuxiliaryInvertibleModel
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.SectionModelRefinement
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.PullbackComp
public import StacksFrontier.AlgebraicGeometry.IdealOfClosedSubscheme.Basic

/-! # The original tensor module comparison through canonical stage refinements

The native pullback tensor composition law identifies the actual tensor model
with the tensor of the two refined original models. No matching isomorphism is
assumed as an additional hypothesis.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.SheafOfModules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The native canonical pullback comparison commutes with the actual tensor
comparison, including the prescribed equality of the original structure maps. -/
theorem canIso_pullbackTensorIso {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (p : W ⟶ Y) (hp : f ≫ g = p) (L N : Y.Modules) :
    canIso f g p hp (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj L).obj N) ≪≫
        Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L N =
      (pullback f).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N) ≪≫
        Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
          ((pullback g).obj L) ((pullback g).obj N) ≪≫
          tensorProductIso W.sheaf.obj W.ringCatSheaf.property
            (canIso f g p hp L) (canIso f g p hp N) := by
  subst p
  apply Iso.ext
  have H := pullbackTensorIso_comp f g L N
  have ht := Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map W.sheaf
    ((pullbackComp f g).hom.app L) ((pullbackComp f g).hom.app N)
  exact H.trans (congrArg
    (fun z => (pullback f).map
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N).hom ≫
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
        ((pullback g).obj L) ((pullback g).obj N)).hom ≫ z) ht)

private theorem tensor_refine_cancel {C : Type*} [Category C] {A B D E F P : C}
    (c : A ≅ B) (t : B ≅ D) (g : A ≅ E) (q : E ≅ F) (d : F ≅ D)
    (e : P ≅ D) (r : P ≅ F) (h : c ≪≫ t = g ≪≫ q ≪≫ d)
    (hr : e ≪≫ d.symm = r) :
    e ≪≫ t.symm ≪≫ c.symm ≪≫ g = r ≪≫ q.symm := by
  have H := congrArg (fun z => z.symm ≪≫ g) h
  have H' : t.symm ≪≫ c.symm ≪≫ g = d.symm ≪≫ q.symm := by
    simpa using H
  calc
    _ = e ≪≫ (t.symm ≪≫ c.symm ≪≫ g) := by rfl
    _ = e ≪≫ (d.symm ≪≫ q.symm) := congrArg (fun z => e ≪≫ z) H'
    _ = (e ≪≫ d.symm) ≪≫ q.symm := (Iso.trans_assoc _ _ _).symm
    _ = _ := congrArg (fun z => z ≪≫ q.symm) hr

/-- Refining the original tensor model and then splitting its pulled-back tensor
is the tensor model built from the same two refined original module isomorphisms. -/
theorem tensorModelIso_refinement {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (p : W ⟶ Y) (hp : f ≫ g = p) (L N : Y.Modules) (M A : W.Modules)
    (eM : M ≅ (pullback p).obj L) (eA : A ≅ (pullback p).obj N) :
    tensorProductIso W.sheaf.obj W.ringCatSheaf.property eM eA ≪≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L N).symm ≪≫
        (canIso f g p hp (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj L).obj N)).symm ≪≫
        (pullback f).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N) =
      tensorProductIso W.sheaf.obj W.ringCatSheaf.property
        (refinedSectionModelIso f g p hp L eM) (refinedSectionModelIso f g p hp N eA) ≪≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
          ((pullback g).obj L) ((pullback g).obj N)).symm := by
  apply tensor_refine_cancel
    (canIso f g p hp (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj L).obj N))
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L N)
    ((pullback f).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N))
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
      ((pullback g).obj L) ((pullback g).obj N))
    (tensorProductIso W.sheaf.obj W.ringCatSheaf.property
      (canIso f g p hp L) (canIso f g p hp N))
  · exact canIso_pullbackTensorIso f g p hp L N
  · exact (Functor.mapIso_trans
      (tensorProductBifunctor W.sheaf.obj W.ringCatSheaf.property)
      (Iso.prod eM eA) (Iso.prod (canIso f g p hp L).symm (canIso f g p hp N).symm)).symm

/-- The actual refined numerator section can be placed in the tensor of the same
refined root and auxiliary modules. Its original model is exactly their tensor
model, not a separately chosen isomorphism. -/
theorem tensorModelIso_refinement_section {W X Y : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (p : W ⟶ Y) (hp : f ≫ g = p)
    (L N : Y.Modules) (M A : W.Modules)
    (eM : M ≅ (pullback p).obj L) (eA : A ≅ (pullback p).obj N)
    (s : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf).obj M).obj A, ⊤))
    (t : Γ((pullback g).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj L).obj N), ⊤))
    (ht : Hom.app
      (refinedSectionModelIso f g p hp
        (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj L).obj N)
        (tensorProductIso W.sheaf.obj W.ringCatSheaf.property eM eA ≪≫
          (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L N).symm)).hom ⊤ s =
      pullbackGlobalSections f _ t) :
    Hom.app
      (tensorProductIso W.sheaf.obj W.ringCatSheaf.property
        (refinedSectionModelIso f g p hp L eM) (refinedSectionModelIso f g p hp N eA) ≪≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
          ((pullback g).obj L) ((pullback g).obj N)).symm).hom ⊤ s =
      pullbackGlobalSections f _
        (Hom.app (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N).hom ⊤ t) := by
  have H := congrArg (fun e => Hom.app (Iso.hom e) ⊤ s)
    (tensorModelIso_refinement f g p hp L N M A eM eA)
  refine H.symm.trans ?_
  change Hom.app ((pullback f).map
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N).hom) ⊤
      (Hom.app
        (refinedSectionModelIso f g p hp
          (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj L).obj N)
          (tensorProductIso W.sheaf.obj W.ringCatSheaf.property eM eA ≪≫
            (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L N).symm)).hom ⊤ s) = _
  exact (congrArg (Hom.app ((pullback f).map
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N).hom) ⊤) ht).trans
      (Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality
        f (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N).hom t).symm

end AlgebraicGeometry.Scheme.Modules
