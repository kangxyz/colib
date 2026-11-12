/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryPowerFrames
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange

/-!
# Power-compatible frames on literal boundary base changes

For a fixed morphism `X ⟶ Y` over an original stage, use the native diagrams of literal
base changes of `X` and `Y`. Their transition maps, boundary maps, limit schemes and comparison
squares are constructed, rather than supplied as additional hypotheses. Quasi-compactness and
quasi-separatedness are needed only for the original boundary `X`. In the curve application
`X` is the whole closed boundary, with all its nilpotents.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Invertible

universe u w w'

namespace Stacks.AlgebraicGeometry.ModuleLimits

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L hL

local instance (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)

set_option maxHeartbeats 800000 in
-- Both the actual over-category base changes and tensor-power comparisons occur in the conclusion.
/-- Simultaneous descent of the actual full-boundary frame, its specified power equations and
linear equations on literal base changes of a fixed boundary morphism. The only limit input is
that of the original base diagram; no compatible scheme diagram is assumed. -/
@[colib_tag "COL-1101"]
theorem exists_baseChange_boundary_frame_power_comp_eq_of_isLimit_finite
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
    ∀ (a : Over i) (M : (C.obj a).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj a).toRingedSpace.presheaf
      (structureSheafRing (C.obj a).toRingedSpace).property M]
    (eLim : (Scheme.Modules.pullback bLim).obj
      ((Scheme.Modules.pullback (cC.π.app a)).obj M) ≅
        SheafOfModules.unit cB.pt.ringCatSheaf),
    let A := (Scheme.Modules.pullback (bt.app a)).obj M
    let U := SheafOfModules.unit (B.obj a).ringCatSheaf
    let N := framePullbackIso (cB.π.app a) (bt.app a) bLim (cC.π.app a) (hb a) M eLim
    ∀ {κ : Type w} [Finite κ] (n : κ → ℕ)
      (α : ∀ x, tensorPower (B.obj a).toRingedSpace.presheaf
          (structureSheafRing (B.obj a).toRingedSpace).property A (n x : ℤ) ⟶
        tensorPower (B.obj a).toRingedSpace.presheaf
          (structureSheafRing (B.obj a).toRingedSpace).property U (n x : ℤ)),
      (∀ x, (pullbackPowerIso (cB.π.app a) A U N (n x)).hom =
        (Scheme.Modules.pullback (cB.π.app a)).map (α x)) →
      ∀ {η : Type w'} [Finite η] (P : η → (B.obj a).Modules)
        [∀ x, (P x).IsFinitePresentation] (s : ∀ x, P x ⟶ A) (t : ∀ x, P x ⟶ U),
        (∀ x, (Scheme.Modules.pullback (cB.π.app a)).map (s x) ≫ N.hom =
          (Scheme.Modules.pullback (cB.π.app a)).map (t x)) →
        ∃ (j : Over i) (f : j ⟶ a)
          (e : (Scheme.Modules.pullback (bt.app j)).obj
            ((Scheme.Modules.pullback (C.map f)).obj M) ≅
              SheafOfModules.unit (B.obj j).ringCatSheaf),
          let m := framePullbackIso (B.map f) (bt.app a) (bt.app j) (C.map f)
            (bt.naturality f) M e
          ((Scheme.Modules.pullback (cB.π.app j)).map m.hom ≫
              canHom (cB.π.app j) (B.map f) (cB.π.app a) (cB.w f) U =
            canHom (cB.π.app j) (B.map f) (cB.π.app a) (cB.w f) A ≫ N.hom) ∧
          (∀ x, (pullbackPowerIso (B.map f) A U m (n x)).hom =
            (Scheme.Modules.pullback (B.map f)).map (α x)) ∧
          ∀ x, (Scheme.Modules.pullback (B.map f)).map (s x) ≫ m.hom =
            (Scheme.Modules.pullback (B.map f)).map (t x) := by
  dsimp only
  intro a M _ eLim κ _ n α hα η _ P _ s t hst
  have : ∀ {j k : Over i} (f : j ⟶ k),
      IsAffineHom ((baseChangeDiagram D i X).map f) :=
    fun f => isAffineHom_baseChangeDiagram_map D i X f
  have : ∀ j, CompactSpace ((baseChangeDiagram D i X).obj j) :=
    compactSpace_baseChangeDiagram_obj D i X
  have : ∀ j, QuasiSeparatedSpace ((baseChangeDiagram D i X).obj j) :=
    quasiSeparatedSpace_baseChangeDiagram_obj D i X
  exact exists_boundary_frame_power_comp_eq_of_isLimit_finite
    (baseChangeDiagram D i X) (baseChangeDiagram D i Y) (baseChangeDiagramMap D i b)
    (baseChangeCone D c i X) (baseChangeConeIsLimit D hc i X)
    (baseChangeCone D c i Y) (baseChangeMap (c.π.app i) X Y b)
    (fun a => (baseChangeCone_π_isPullback D i b c a).w) a M eLim n α hα P s t hst

end Stacks.AlgebraicGeometry.ModuleLimits
