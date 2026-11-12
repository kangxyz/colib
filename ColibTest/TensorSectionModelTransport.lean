/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.TensorSectionModelTransport

/-! # Same original numerator under actual direct-root refinement -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.SheafOfModules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Modules

example {X Y : Scheme.{u}} (p : X ⟶ Y)
    {L N L' N' : Y.Modules} {M A : X.Modules}
    (E : M ≅ (pullback p).obj L) (F : A ≅ (pullback p).obj N)
    (l : L ≅ L') (n : N ≅ N') :
    tensorProductIso X.sheaf.obj X.ringCatSheaf.property
        (E ≪≫ (pullback p).mapIso l) (F ≪≫ (pullback p).mapIso n) ≪≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L' N').symm =
      tensorProductIso X.sheaf.obj X.ringCatSheaf.property E F ≪≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L N).symm ≪≫
        (pullback p).mapIso (tensorProductIso Y.sheaf.obj Y.ringCatSheaf.property l n) :=
  tensorSectionModelIso_transport p E F l n

#print axioms tensorSectionModelIso_transport

example {X Y : Scheme.{u}} (p : X ⟶ Y)
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
        (Hom.app (tensorProductIso Y.sheaf.obj Y.ringCatSheaf.property l n).hom ⊤ t) :=
  tensorSectionModelIso_transport_section p E F l n s t ht

#print axioms tensorSectionModelIso_transport_section

end AlgebraicGeometry.Scheme.Modules
