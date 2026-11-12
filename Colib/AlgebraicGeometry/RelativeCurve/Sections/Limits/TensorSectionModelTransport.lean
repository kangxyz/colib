/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.TensorModelRefinement
public import Colib.AlgebraicGeometry.Modules.Invertible.UnitPowerPullback

/-! # Transport the same tensor section model through actual stage isomorphisms

Canonical stage comparisons can replace nested root pullbacks by the direct root
pullback while retaining the original numerator and auxiliary module model.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.SheafOfModules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem tensor_transport_aux {C : Type*} [Category C] {A B D E F : C}
    (e : A ≅ B) (e' : A ≅ D) (t : E ≅ B) (t' : F ≅ D) (k : E ≅ F) (d : B ≅ D)
    (he : e ≪≫ d = e') (hk : k ≪≫ t' = t ≪≫ d) :
    e' ≪≫ t'.symm = e ≪≫ t.symm ≪≫ k := by
  have H := congrArg (fun z => t.symm ≪≫ z ≪≫ t'.symm) hk
  have H' : t.symm ≪≫ k = d ≪≫ t'.symm := by simpa [Iso.trans_assoc] using H
  rw [H', ← Iso.trans_assoc, he]

/-- Stage model isomorphisms transport the tensor model of the same original
factors through precisely their actual pulled-back tensor isomorphism. -/
theorem tensorSectionModelIso_transport {X Y : Scheme.{u}} (p : X ⟶ Y)
    {L N L' N' : Y.Modules} {M A : X.Modules}
    (E : M ≅ (pullback p).obj L) (F : A ≅ (pullback p).obj N)
    (l : L ≅ L') (n : N ≅ N') :
    tensorProductIso X.sheaf.obj X.ringCatSheaf.property
        (E ≪≫ (pullback p).mapIso l) (F ≪≫ (pullback p).mapIso n) ≪≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L' N').symm =
      tensorProductIso X.sheaf.obj X.ringCatSheaf.property E F ≪≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L N).symm ≪≫
        (pullback p).mapIso (tensorProductIso Y.sheaf.obj Y.ringCatSheaf.property l n) := by
  apply tensor_transport_aux
    (tensorProductIso X.sheaf.obj X.ringCatSheaf.property E F) _
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L N)
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L' N') _
    (tensorProductIso X.sheaf.obj X.ringCatSheaf.property
      ((pullback p).mapIso l) ((pullback p).mapIso n))
  · exact (Functor.mapIso_trans (tensorProductBifunctor X.sheaf.obj X.ringCatSheaf.property)
      (Iso.prod E F) (Iso.prod ((pullback p).mapIso l) ((pullback p).mapIso n))).symm
  · exact pullbackTensorIso_tensorProductIso p l n

/-- The actual transported stage numerator still recovers the same original
numerator through the tensor of the two transported original factor models. -/
theorem tensorSectionModelIso_transport_section {X Y : Scheme.{u}} (p : X ⟶ Y)
    {L N L' N' : Y.Modules} {M A : X.Modules}
    (E : M ≅ (pullback p).obj L) (F : A ≅ (pullback p).obj N)
    (l : L ≅ L') (n : N ≅ N')
    (s : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj A, ⊤))
    (t : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj L).obj N, ⊤))
    (ht : Hom.app (tensorProductIso X.sheaf.obj X.ringCatSheaf.property E F ≪≫
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L N).symm).hom ⊤ s =
        pullbackGlobalSections p _ t) :
    Hom.app (tensorProductIso X.sheaf.obj X.ringCatSheaf.property
        (E ≪≫ (pullback p).mapIso l) (F ≪≫ (pullback p).mapIso n) ≪≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L' N').symm).hom ⊤ s =
      pullbackGlobalSections p _
        (Hom.app (tensorProductIso Y.sheaf.obj Y.ringCatSheaf.property l n).hom ⊤ t) := by
  have H := congrArg (fun e => Hom.app (Iso.hom e) ⊤ s)
    (tensorSectionModelIso_transport p E F l n)
  refine H.trans ?_
  change Hom.app ((pullback p).map
    (tensorProductIso Y.sheaf.obj Y.ringCatSheaf.property l n).hom) ⊤
      (Hom.app (tensorProductIso X.sheaf.obj X.ringCatSheaf.property E F ≪≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L N).symm).hom ⊤ s) = _
  exact (congrArg (Hom.app ((pullback p).map
    (tensorProductIso Y.sheaf.obj Y.ringCatSheaf.property l n).hom) ⊤) ht).trans
      (Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality p
        (tensorProductIso Y.sheaf.obj Y.ringCatSheaf.property l n).hom t).symm

end AlgebraicGeometry.Scheme.Modules
