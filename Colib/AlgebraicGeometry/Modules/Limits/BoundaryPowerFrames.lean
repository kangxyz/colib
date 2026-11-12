/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryFrames
public import Colib.AlgebraicGeometry.Modules.Limits.TensorPowerIsomorphisms
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Basic

/-!
# Full-boundary frames with simultaneous power and section equations

An invertible module already descended to an ambient stage may be used here, including the
actual module supplied by root descent. A frame is only given on the limit boundary. The
specified tensor-power morphisms and prescribed section equations all descend with that frame,
on the entire boundary and at the same transition. The equations use the native canonical
pullback and tensor-power comparisons, without replacing the original boundary scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Invertible

universe u v w w'

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

/-- The specified ambient power isomorphism and boundary trivialization, expressed as a
map to the power of the boundary structure sheaf. This retains both original isomorphisms;
its pullback is a concrete power equation accepted by the frame descent theorem below. -/
def boundaryRootPowerIso {X Y : Scheme.{u}} (b : X ⟶ Y) (M L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M] (n : ℕ)
    (α : tensorPower Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property
      M (n : ℤ) ≅ L)
    (τ : (Scheme.Modules.pullback b).obj L ≅ SheafOfModules.unit X.ringCatSheaf) :
    tensorPower X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
        ((Scheme.Modules.pullback b).obj M) (n : ℤ) ≅
      tensorPower X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
        (SheafOfModules.unit X.ringCatSheaf) (n : ℤ) :=
  (Scheme.Modules.pullbackTensorPowerIso b M n).symm ≪≫
    (Scheme.Modules.pullback b).mapIso α ≪≫ τ ≪≫ (structureSheafTensorPowerIso X n).symm

private theorem normalize_frame {C : Type*} [Category C] {A B U V : C}
    (S : A ≅ B) (m : A ≅ U) (u : U ≅ V) :
    S ≪≫ (S.symm ≪≫ m ≪≫ u) ≪≫ u.symm = m := by
  simp

set_option maxHeartbeats 600000 in
-- The frame is compared in three module categories through the same original scheme square.
/-- A given full-boundary frame descends with specified power maps and finitely many linear
equations. The power morphisms need not be isomorphisms; an actual root isomorphism restricted
to the boundary is one important instance. No boundary frame at a stage is an input. -/
@[colib_tag "COL-1101"]
theorem exists_boundary_frame_power_comp_eq_of_isLimit_finite
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    (B C : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
    (b : B ⟶ C) (cB : Cone B) (hcB : IsLimit cB)
    [∀ i, CompactSpace (B.obj i)] [∀ i, QuasiSeparatedSpace (B.obj i)]
    (cC : Cone C) (bLim : cB.pt ⟶ cC.pt)
    (hb : ∀ i, cB.π.app i ≫ b.app i = bLim ≫ cC.π.app i)
    (i : I) (M : (C.obj i).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj i).toRingedSpace.presheaf
      (structureSheafRing (C.obj i).toRingedSpace).property M]
    (eLim : (Scheme.Modules.pullback bLim).obj
      ((Scheme.Modules.pullback (cC.π.app i)).obj M) ≅
        SheafOfModules.unit cB.pt.ringCatSheaf) :
    let A := (Scheme.Modules.pullback (b.app i)).obj M
    let U := SheafOfModules.unit (B.obj i).ringCatSheaf
    let N := framePullbackIso (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M eLim
    ∀ {κ : Type w} [Finite κ] (n : κ → ℕ)
      (α : ∀ x, tensorPower (B.obj i).toRingedSpace.presheaf
          (structureSheafRing (B.obj i).toRingedSpace).property A (n x : ℤ) ⟶
        tensorPower (B.obj i).toRingedSpace.presheaf
          (structureSheafRing (B.obj i).toRingedSpace).property U (n x : ℤ)),
      (∀ x, (pullbackPowerIso (cB.π.app i) A U N (n x)).hom =
        (Scheme.Modules.pullback (cB.π.app i)).map (α x)) →
      ∀ {η : Type w'} [Finite η] (P : η → (B.obj i).Modules)
        [∀ x, (P x).IsFinitePresentation] (s : ∀ x, P x ⟶ A) (t : ∀ x, P x ⟶ U),
        (∀ x, (Scheme.Modules.pullback (cB.π.app i)).map (s x) ≫ N.hom =
          (Scheme.Modules.pullback (cB.π.app i)).map (t x)) →
        ∃ (j : I) (f : j ⟶ i)
          (e : (Scheme.Modules.pullback (b.app j)).obj
            ((Scheme.Modules.pullback (C.map f)).obj M) ≅
              SheafOfModules.unit (B.obj j).ringCatSheaf),
          let m := framePullbackIso (B.map f) (b.app i) (b.app j) (C.map f)
            (b.naturality f) M e
          ((Scheme.Modules.pullback (cB.π.app j)).map m.hom ≫
              canHom (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f) U =
            canHom (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f) A ≫ N.hom) ∧
          (∀ x, (pullbackPowerIso (B.map f) A U m (n x)).hom =
            (Scheme.Modules.pullback (B.map f)).map (α x)) ∧
          ∀ x, (Scheme.Modules.pullback (B.map f)).map (s x) ≫ m.hom =
            (Scheme.Modules.pullback (B.map f)).map (t x) := by
  dsimp only
  intro κ _ n α hα η _ P _ s t hst
  obtain ⟨j, f, m, hm, hmα, hmt⟩ :=
    exists_iso_pullback_power_comp_eq_of_isLimit_finite B cB hcB i
      ((Scheme.Modules.pullback (b.app i)).obj M)
      (SheafOfModules.unit (B.obj i).ringCatSheaf)
      (framePullbackIso (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M eLim)
      n α hα P s t hst
  let S := pullbackSquareIso (B.map f) (b.app i) (b.app j) (C.map f) (b.naturality f) M
  let e := S.symm ≪≫ m ≪≫ Scheme.Modules.pullbackUnitIso (B.map f)
  have he : framePullbackIso (B.map f) (b.app i) (b.app j) (C.map f)
      (b.naturality f) M e = m := normalize_frame S m (Scheme.Modules.pullbackUnitIso _)
  refine ⟨j, f, e, ?_⟩
  simpa only [he] using And.intro hm (And.intro hmα hmt)

end Stacks.AlgebraicGeometry.ModuleLimits
