module

import Colib.AlgebraicGeometry.Modules.Limits.BoundaryPowerFrames

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.SheafOfModules.Invertible

universe u

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

-- The original ambient square root and original full-boundary trivialization are retained.
-- No reduction, residue-field test, local stage, or stage frame occurs among the hypotheses.
example {I : Type u} [Category.{u} I] [IsCofiltered I]
    (B C : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
    (b : B ⟶ C) (cB : Cone B) (hcB : IsLimit cB)
    [∀ i, CompactSpace (B.obj i)] [∀ i, QuasiSeparatedSpace (B.obj i)]
    (cC : Cone C) (bLim : cB.pt ⟶ cC.pt)
    (hb : ∀ i, cB.π.app i ≫ b.app i = bLim ≫ cC.π.app i)
    (i : I) (M L : (C.obj i).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj i).toRingedSpace.presheaf
      (structureSheafRing (C.obj i).toRingedSpace).property M]
    (β : tensorPower (C.obj i).toRingedSpace.presheaf
      (structureSheafRing (C.obj i).toRingedSpace).property M (2 : ℤ) ≅ L)
    (τ : (Scheme.Modules.pullback (b.app i)).obj L ≅
      SheafOfModules.unit (B.obj i).ringCatSheaf)
    (eLim : (Scheme.Modules.pullback bLim).obj
      ((Scheme.Modules.pullback (cC.π.app i)).obj M) ≅
        SheafOfModules.unit cB.pt.ringCatSheaf) :
    let A := (Scheme.Modules.pullback (b.app i)).obj M
    let U := SheafOfModules.unit (B.obj i).ringCatSheaf
    let N := framePullbackIso (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M eLim
    let α := boundaryRootPowerIso (b.app i) M L 2 β τ
    (pullbackPowerIso (cB.π.app i) A U N 2).hom =
        (Scheme.Modules.pullback (cB.π.app i)).map α.hom →
      ∃ (j : I) (f : j ⟶ i)
        (e : (Scheme.Modules.pullback (b.app j)).obj
          ((Scheme.Modules.pullback (C.map f)).obj M) ≅
            SheafOfModules.unit (B.obj j).ringCatSheaf),
        (pullbackPowerIso (B.map f) A U
          (framePullbackIso (B.map f) (b.app i) (b.app j) (C.map f) (b.naturality f) M e)
          2).hom = (Scheme.Modules.pullback (B.map f)).map α.hom := by
  dsimp only
  intro hα
  have : (SheafOfModules.unit (B.obj i).ringCatSheaf).IsFinitePresentation :=
    isFinitePresentation_unit _
  obtain ⟨j, f, e, _, he, _⟩ := exists_boundary_frame_power_comp_eq_of_isLimit_finite
    B C b cB hcB cC bLim hb i M eLim (fun _ : Unit => 2)
    (fun _ => (boundaryRootPowerIso (b.app i) M L 2 β τ).hom) (fun _ => hα)
    (fun _ : Empty => SheafOfModules.unit (B.obj i).ringCatSheaf)
    (fun x => nomatch x) (fun x => nomatch x) (fun x => nomatch x)
  exact ⟨j, f, e, he ()⟩
