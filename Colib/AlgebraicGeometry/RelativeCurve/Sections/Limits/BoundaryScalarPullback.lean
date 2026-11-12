/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.BoundarySectionEquations
public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryRoot
public import StacksFrontier.AlgebraicGeometry.IdealOfClosedSubscheme.Basic

/-! # Full-boundary scalar one survives the actual square pullback

The same boundary frame and section are pulled back along the prescribed square.
Their scalar normalization is preserved, without a newly chosen frame or section.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Literal square pullback of a frame and section preserves their full-boundary
value one. This also preserves denominator normalization after root descent. -/
theorem pullbackBoundaryTrivialization_section_one {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D)
    (w : f ≫ g = h ≫ k) (N : D.Modules)
    (e : (pullback g).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (s : Γ(N, ⊤))
    (hs : Hom.app e.hom ⊤ (pullbackGlobalSections g N s) = (1 : Γ(B, ⊤))) :
    Hom.app (pullbackBoundaryTrivialization f g h k w N e).hom ⊤
      (pullbackGlobalSections h _ (pullbackGlobalSections k N s)) = (1 : Γ(A, ⊤)) := by
  have hp := pullbackSquareIso_pullbackGlobalSections f g h k w N s
  have hi : Hom.app (pullbackSquareIso f g h k w N).inv ⊤
      (pullbackGlobalSections h _ (pullbackGlobalSections k N s)) =
      pullbackGlobalSections f _ (pullbackGlobalSections g N s) :=
    (congrArg (Hom.app (pullbackSquareIso f g h k w N).inv ⊤) hp).symm.trans
      (app_inv_app (pullbackSquareIso f g h k w N) ⊤ _)
  change Hom.app (pullbackUnitIso f).hom ⊤
    (Hom.app ((pullback f).map e.hom) ⊤
      (Hom.app (pullbackSquareIso f g h k w N).inv ⊤
        (pullbackGlobalSections h _ (pullbackGlobalSections k N s)))) = _
  have hn := Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality
    f e.hom (pullbackGlobalSections g N s)
  exact (congrArg (fun z => Hom.app (pullbackUnitIso f).hom ⊤
    (Hom.app ((pullback f).map e.hom) ⊤ z)) hi).trans
      ((congrArg (Hom.app (pullbackUnitIso f).hom ⊤) hn.symm).trans
        ((congrArg (fun z => Hom.app (pullbackUnitIso f).hom ⊤
          (pullbackGlobalSections f (SheafOfModules.unit B.ringCatSheaf) z)) hs).trans
            ((SectionsEqualizer.pullbackUnitIso_unit f (1 : Γ(B, ⊤))).trans
              (map_one f.appTop.hom))))

end AlgebraicGeometry.Scheme.Modules
