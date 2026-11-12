/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryFrames
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange

/-!
# Frames on literal base changes of a fixed full boundary

For a fixed morphism `X ⟶ Y` over an original stage, use the native diagrams of literal
base changes of `X` and `Y`. Their transition maps, boundary maps, limit schemes and comparison
squares are constructed, rather than supplied as additional hypotheses. Quasi-compactness and
quasi-separatedness are needed only for the original boundary `X`. In the curve application
`X` is the whole closed boundary, with all its nilpotents.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w

namespace Stacks.AlgebraicGeometry.ModuleLimits

set_option maxHeartbeats 800000 in
-- The statement identifies the native over-category diagrams with their literal pullbacks.
/-- A frame on the full boundary of a limit base change descends to a literal base change
of the original boundary morphism. All geometric diagrams and their limit witnesses are
supplied by the native base-change construction. Finitely many equations descend with it. -/
@[colib_tag "COL-1101", colib_ref "axiom_stacks_5ed82d14"
  "AlgebraicGeometry/Limits/DescendingMorphisms/BaseChange.lean:276-420"
  "ingredient" "Actual base-change diagrams, their limit cones and boundary comparison squares"]
theorem exists_baseChange_boundary_frame_comp_eq_of_isLimit_finite
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : I) (X Y : Over (D.obj i)) (b : X ⟶ Y)
    [CompactSpace X.left] [QuasiSeparatedSpace X.left] :
    let B := baseChangeDiagram D i X
    let C := baseChangeDiagram D i Y
    let cB := baseChangeCone D c i X
    let cC := baseChangeCone D c i Y
    let bt := baseChangeDiagramMap D i b
    let bLim := baseChangeMap (c.π.app i) X Y b
    let hb := fun a => (baseChangeCone_π_isPullback D i b c a).w
    ∀ (a : Over i) (M : (C.obj a).Modules) [M.IsFinitePresentation]
      (eLim : (Scheme.Modules.pullback bLim).obj
        ((Scheme.Modules.pullback (cC.π.app a)).obj M) ≅
          SheafOfModules.unit cB.pt.ringCatSheaf)
      {κ : Type w} [Finite κ] (P : κ → (B.obj a).Modules)
      [∀ x, (P x).IsFinitePresentation]
      (s : ∀ x, P x ⟶ (Scheme.Modules.pullback (bt.app a)).obj M)
      (t : ∀ x, P x ⟶ SheafOfModules.unit (B.obj a).ringCatSheaf),
      (∀ x, (Scheme.Modules.pullback (cB.π.app a)).map (s x) ≫
          (pullbackSquareIso (cB.π.app a) (bt.app a) bLim (cC.π.app a) (hb a) M).hom ≫
          eLim.hom = (Scheme.Modules.pullback (cB.π.app a)).map (t x) ≫
            (Scheme.Modules.pullbackUnitIso (cB.π.app a)).hom) →
      ∃ (j : Over i) (f : j ⟶ a)
        (e : (Scheme.Modules.pullback (baseChangeMap (D.map j.hom) X Y b)).obj
          ((Scheme.Modules.pullback (C.map f)).obj M) ≅
            SheafOfModules.unit (B.obj j).ringCatSheaf),
        ((Scheme.Modules.pullback (cB.π.app j)).map
            ((pullbackSquareIso (B.map f) (bt.app a) (bt.app j) (C.map f)
              (bt.naturality f) M).hom ≫ e.hom) ≫
            (Scheme.Modules.pullbackUnitIso (cB.π.app j)).hom =
          canHom (cB.π.app j) (B.map f) (cB.π.app a) (cB.w f)
            ((Scheme.Modules.pullback (bt.app a)).obj M) ≫
            (pullbackSquareIso (cB.π.app a) (bt.app a) bLim (cC.π.app a) (hb a) M).hom ≫
            eLim.hom) ∧
        ∀ x, (Scheme.Modules.pullback (B.map f)).map (s x) ≫
            (pullbackSquareIso (B.map f) (bt.app a) (bt.app j) (C.map f)
              (bt.naturality f) M).hom ≫ e.hom =
          (Scheme.Modules.pullback (B.map f)).map (t x) ≫
            (Scheme.Modules.pullbackUnitIso (B.map f)).hom := by
  dsimp only
  intro a M _ eLim κ _ P _ s t hst
  have : ∀ {j k : Over i} (f : j ⟶ k),
      IsAffineHom ((baseChangeDiagram D i X).map f) :=
    fun f => isAffineHom_baseChangeDiagram_map D i X f
  have : ∀ j, CompactSpace ((baseChangeDiagram D i X).obj j) :=
    compactSpace_baseChangeDiagram_obj D i X
  have : ∀ j, QuasiSeparatedSpace ((baseChangeDiagram D i X).obj j) :=
    quasiSeparatedSpace_baseChangeDiagram_obj D i X
  exact exists_boundary_frame_comp_eq_of_isLimit_finite
    (baseChangeDiagram D i X) (baseChangeDiagram D i Y) (baseChangeDiagramMap D i b)
    (baseChangeCone D c i X) (baseChangeConeIsLimit D hc i X)
    (baseChangeCone D c i Y) (baseChangeMap (c.π.app i) X Y b)
    (fun a => (baseChangeCone_π_isPullback D i b c a).w) a M eLim P s t hst

end Stacks.AlgebraicGeometry.ModuleLimits
