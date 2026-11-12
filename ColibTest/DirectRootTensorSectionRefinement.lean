/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.DirectRootTensorSectionRefinement

/-! # Same original numerator under actual direct-root refinement -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.SheafOfModules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Modules

example {W X Y Z : Scheme.{u}}
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
            ((pullback h).obj L) N).hom ⊤ t)) :=
  directRootTensorSection_refinement f g h p r q hfg hgh hph hfr L N M A E F a t ht

#print axioms directRootTensorSection_refinement

end AlgebraicGeometry.Scheme.Modules
