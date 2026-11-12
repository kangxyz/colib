/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryRootTransport

/-!
# Root-frame compatibility after a prescribed refinement

The original canonical pullback comparisons transport the same root and full-boundary frame
through any prescribed intermediate square. This lets finite auxiliary data be selected after
the root model, without selecting another root.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.SheafOfModules.Invertible

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L hL

private theorem root_can_aux {D : Type*} [Category D] {A B C D' E X Y : D}
    (a : A ≅ B) (b : B ≅ C) (c : A ≅ D') (d : D' ≅ E) (r : C ≅ E)
    (x : A ≅ X) (y : D' ≅ Y) (t : X ≅ Y)
    (hc : c.symm ≪≫ a ≪≫ b ≪≫ r = d) (hn : x ≪≫ t = c ≪≫ y) :
    b.symm ≪≫ a.symm ≪≫ x ≪≫ t = r ≪≫ d.symm ≪≫ y := by
  have hz : b.symm ≪≫ a.symm ≪≫ c = r ≪≫ d.symm := by
    simpa [Iso.trans_assoc] using
      (congrArg (fun z => b.symm ≪≫ a.symm ≪≫ c ≪≫ z ≪≫ d.symm) hc).symm
  rw [hn]
  simpa only [Iso.trans_assoc] using congrArg (fun z => z ≪≫ y) hz

private theorem root_can_map_aux {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C' : C} {P Q : D} (a : A ≅ B) (b : A ≅ C') (p : F.obj B ≅ P)
    (l : F.obj C' ≅ Q) :
    (p.symm ≪≫ F.mapIso (a.symm ≪≫ b)) ≪≫ l =
      p.symm ≪≫ (F.mapIso a).symm ≪≫ F.mapIso b ≪≫ l := by
  simp [Iso.trans_assoc]

/-- The pulled back root isomorphism agrees with its original named composite. -/
theorem pullback_root_iso_can {X Y Z : Scheme.{u}} (q : X ⟶ Y) (f : Y ⟶ Z)
    (p : X ⟶ Z) (hp : q ≫ f = p) (M L : Z.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z.toRingedSpace.presheaf
      (structureSheafRing Z.toRingedSpace).property M] (n : ℕ)
    (α : tensorPower Z.toRingedSpace.presheaf (structureSheafRing Z.toRingedSpace).property
      M (n : ℤ) ≅ L) :
    ((Scheme.Modules.pullbackTensorPowerIso q ((Scheme.Modules.pullback f).obj M) n).symm ≪≫
      (Scheme.Modules.pullback q).mapIso
        ((Scheme.Modules.pullbackTensorPowerIso f M n).symm ≪≫
          (Scheme.Modules.pullback f).mapIso α)) ≪≫ canIso q f p hp L =
    tensorPowerCongr X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
      _ _ (canIso q f p hp M) n ≪≫
      (Scheme.Modules.pullbackTensorPowerIso p M n).symm ≪≫
        (Scheme.Modules.pullback p).mapIso α := by
  have h := root_can_aux
    ((Scheme.Modules.pullback q).mapIso (Scheme.Modules.pullbackTensorPowerIso f M n))
    (Scheme.Modules.pullbackTensorPowerIso q ((Scheme.Modules.pullback f).obj M) n)
    (canIso q f p hp (tensorPower Z.toRingedSpace.presheaf
      (structureSheafRing Z.toRingedSpace).property M (n : ℤ)))
    (Scheme.Modules.pullbackTensorPowerIso p M n)
    (tensorPowerCongr X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
      _ _ (canIso q f p hp M) n)
    ((Scheme.Modules.pullback q).mapIso ((Scheme.Modules.pullback f).mapIso α))
    ((Scheme.Modules.pullback p).mapIso α) (canIso q f p hp L)
    (pullbackTensorPowerIso_can q f p hp M n)
    (Iso.ext (canHom_naturality q f p hp α.hom))
  exact (root_can_map_aux (Scheme.Modules.pullback q)
    (Scheme.Modules.pullbackTensorPowerIso f M n) ((Scheme.Modules.pullback f).mapIso α)
    (Scheme.Modules.pullbackTensorPowerIso q ((Scheme.Modules.pullback f).obj M) n)
    (canIso q f p hp L)).trans h

local instance (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)

/-- The same original frame remains compatible after any specified intermediate square. -/
theorem boundary_root_frame_refine {A B C A' B' C' : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (s : A ⟶ C)
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (p : A' ⟶ B') (q : B' ⟶ C') (r : A' ⟶ C')
    (hfg : f ≫ g = s) (hpq : p ≫ q = r)
    (hf : f ≫ b = a ≫ p) (hg : g ≫ c = b ≫ q) (hs : s ≫ c = a ≫ r)
    (M L : C'.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible C'.toRingedSpace.presheaf
      (structureSheafRing C'.toRingedSpace).property M] (n : ℕ)
    (α : tensorPower C'.toRingedSpace.presheaf (structureSheafRing C'.toRingedSpace).property
      M (n : ℤ) ≅ L)
    (τ : (Scheme.Modules.pullback c).obj L ≅ SheafOfModules.unit C.ringCatSheaf)
    (e : (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback r).obj M) ≅
      SheafOfModules.unit A.ringCatSheaf)
    (he : tensorPowerCongr A.toRingedSpace.presheaf
      (structureSheafRing A.toRingedSpace).property _ _ e n =
        boundaryRootPowerIso a ((Scheme.Modules.pullback r).obj M)
          ((Scheme.Modules.pullback r).obj L) n
          ((Scheme.Modules.pullbackTensorPowerIso r M n).symm ≪≫
            (Scheme.Modules.pullback r).mapIso α)
          (pullbackBoundaryTrivialization s c a r hs L τ)) :
    tensorPowerCongr A.toRingedSpace.presheaf
      (structureSheafRing A.toRingedSpace).property _ _
      ((Scheme.Modules.pullback a).mapIso (canIso p q r hpq M) ≪≫ e) n =
    boundaryRootPowerIso a
      ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj M))
      ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj L)) n
      ((Scheme.Modules.pullbackTensorPowerIso p ((Scheme.Modules.pullback q).obj M) n).symm ≪≫
        (Scheme.Modules.pullback p).mapIso
          ((Scheme.Modules.pullbackTensorPowerIso q M n).symm ≪≫
            (Scheme.Modules.pullback q).mapIso α))
      (pullbackBoundaryTrivialization f b a p hf ((Scheme.Modules.pullback q).obj L)
        (pullbackBoundaryTrivialization g c b q hg L τ)) := by
  have h := boundary_root_frame_transport a _ _ _ _ (canIso p q r hpq M) n _ _
    (canIso p q r hpq L) (pullbackBoundaryTrivialization s c a r hs L τ) e
    (pullback_root_iso_can p q r hpq M L n α) he
  exact h.trans (congrArg (boundaryRootPowerIso a _ _ n _)
    (pullbackBoundaryTrivialization_comp f g s a b c p q r hfg hpq hf hg hs L τ).symm)

end Stacks.AlgebraicGeometry.ModuleLimits
