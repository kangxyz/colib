/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryPowerFrames
public import Colib.AlgebraicGeometry.Modules.Invertible.UnitPowerPullback
public import Colib.AlgebraicGeometry.Modules.Invertible.LimitRoot

/-!
# Original boundary-square comparisons for tensor roots

The actual square comparison is compatible with natural tensor powers. These equations retain
both original paths and are used to transport a specified root and its full-boundary frame.
No boundary is replaced by its reduction and no stage is assumed local or integral.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Invertible
universe u
namespace Stacks.AlgebraicGeometry.ModuleLimits
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L hL

/-- The original canonical pullback comparison commutes with tensor powers. -/
theorem pullbackTensorPowerIso_can {X Y Z : Scheme.{u}} (q : X ⟶ Y) (f : Y ⟶ Z)
    (p : X ⟶ Z) (hp : q ≫ f = p) (M : Z.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z.toRingedSpace.presheaf
      (structureSheafRing Z.toRingedSpace).property M] (n : ℕ) :
    (canIso q f p hp (tensorPower Z.toRingedSpace.presheaf
      (structureSheafRing Z.toRingedSpace).property M (n : ℤ))).symm ≪≫
      (Scheme.Modules.pullback q).mapIso (Scheme.Modules.pullbackTensorPowerIso f M n) ≪≫
      Scheme.Modules.pullbackTensorPowerIso q ((Scheme.Modules.pullback f).obj M) n ≪≫
      tensorPowerCongr X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
        _ _ (canIso q f p hp M) n = Scheme.Modules.pullbackTensorPowerIso p M n := by
  subst p
  have hcan (L : Z.Modules) : canIso q f (q ≫ f) rfl L =
      (Scheme.Modules.pullbackComp q f).app L := Iso.ext (canHom_rfl q f L)
  simp only [hcan]
  exact Iso.ext (Scheme.Modules.pullbackTensorPowerIso_comp q f M n)

private theorem square_power_aux {D : Type*} [Category D] {A B P X Y Q : D}
    (c : A ≅ P) (d : B ≅ P) (a : A ≅ X) (b : B ≅ Y) (s : X ≅ Q) (t : Y ≅ Q)
    (h : c.symm ≪≫ a ≪≫ s = d.symm ≪≫ b ≪≫ t) :
    a ≪≫ s ≪≫ t.symm = c ≪≫ d.symm ≪≫ b := by
  simpa only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.self_symm_id,
    Iso.trans_refl] using congrArg (fun z => c ≪≫ z ≪≫ t.symm) h

/-- The two original paths through a commutative scheme square induce the same comparison
on tensor powers after transporting by the power of the actual square isomorphism. -/
theorem pullbackSquareIso_tensorPower {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D) (w : f ≫ g = h ≫ k)
    (M : D.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible D.toRingedSpace.presheaf
      (structureSheafRing D.toRingedSpace).property M] (n : ℕ) :
    (Scheme.Modules.pullback f).mapIso (Scheme.Modules.pullbackTensorPowerIso g M n) ≪≫
      Scheme.Modules.pullbackTensorPowerIso f ((Scheme.Modules.pullback g).obj M) n ≪≫
      tensorPowerCongr A.toRingedSpace.presheaf (structureSheafRing A.toRingedSpace).property
        _ _ (pullbackSquareIso f g h k w M) n =
    pullbackSquareIso f g h k w (tensorPower D.toRingedSpace.presheaf
      (structureSheafRing D.toRingedSpace).property M (n : ℤ)) ≪≫
      (Scheme.Modules.pullback h).mapIso (Scheme.Modules.pullbackTensorPowerIso k M n) ≪≫
      Scheme.Modules.pullbackTensorPowerIso h ((Scheme.Modules.pullback k).obj M) n := by
  let c := canIso f g (h ≫ k) w M
  let d := canIso h k (h ≫ k) rfl M
  have hp := (tensorPowerCongr_trans A.toRingedSpace.presheaf
    (structureSheafRing A.toRingedSpace).property c d.symm n).trans
      (congrArg (fun z => tensorPowerCongr A.toRingedSpace.presheaf
        (structureSheafRing A.toRingedSpace).property _ _ c n ≪≫ z)
        (tensorPowerCongr_symm A.toRingedSpace.presheaf
          (structureSheafRing A.toRingedSpace).property d n))
  have hs := square_power_aux
    (canIso f g (h ≫ k) w (tensorPower D.toRingedSpace.presheaf
      (structureSheafRing D.toRingedSpace).property M (n : ℤ)))
    (canIso h k (h ≫ k) rfl (tensorPower D.toRingedSpace.presheaf
      (structureSheafRing D.toRingedSpace).property M (n : ℤ)))
    ((Scheme.Modules.pullback f).mapIso (Scheme.Modules.pullbackTensorPowerIso g M n) ≪≫
      Scheme.Modules.pullbackTensorPowerIso f ((Scheme.Modules.pullback g).obj M) n)
    ((Scheme.Modules.pullback h).mapIso (Scheme.Modules.pullbackTensorPowerIso k M n) ≪≫
      Scheme.Modules.pullbackTensorPowerIso h ((Scheme.Modules.pullback k).obj M) n)
    _ _ ((pullbackTensorPowerIso_can f g (h ≫ k) w M n).trans
      (pullbackTensorPowerIso_can h k (h ≫ k) rfl M n).symm)
  have hh := congrArg (fun z =>
    ((Scheme.Modules.pullback f).mapIso (Scheme.Modules.pullbackTensorPowerIso g M n) ≪≫
      Scheme.Modules.pullbackTensorPowerIso f ((Scheme.Modules.pullback g).obj M) n) ≪≫ z) hp
  exact (Iso.trans_assoc _ _ _).symm.trans (hh.trans hs)
private theorem square_iso_naturality_aux {D : Type*} [Category D]
    {M1 M2 M0 L1 L2 L0 : D} (cM : M1 ≅ M0) (cL : L1 ≅ L0)
    (dM : M2 ≅ M0) (dL : L2 ≅ L0) (a : M1 ≅ L1) (b : M2 ≅ L2) (z : M0 ≅ L0)
    (ha : a ≪≫ cL = cM ≪≫ z) (hb : b ≪≫ dL = dM ≪≫ z) :
    a ≪≫ cL ≪≫ dL.symm = cM ≪≫ dM.symm ≪≫ b := by
  have hm := congrArg (fun v => dM.symm ≪≫ v ≪≫ dL.symm) hb
  simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl,
    Iso.symm_self_id_assoc] at hm
  have hh := congrArg (fun v => v ≪≫ dL.symm) ha
  simp only [Iso.trans_assoc] at hh
  exact hh.trans (congrArg (fun v => cM ≪≫ v) hm.symm)

set_option maxHeartbeats 600000 in
-- The two naturality squares compare four original iterated pullbacks.
/-- Naturality of the original boundary-square isomorphism, retaining both original paths. -/
theorem pullbackSquareIso_naturality {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D) (w : f ≫ g = h ≫ k)
    {M L : D.Modules} (α : M ≅ L) :
    (Scheme.Modules.pullback f).mapIso ((Scheme.Modules.pullback g).mapIso α) ≪≫
        pullbackSquareIso f g h k w L =
      pullbackSquareIso f g h k w M ≪≫
        (Scheme.Modules.pullback h).mapIso ((Scheme.Modules.pullback k).mapIso α) := by
  exact square_iso_naturality_aux
    (canIso f g (h ≫ k) w M) (canIso f g (h ≫ k) w L)
    (canIso h k (h ≫ k) rfl M) (canIso h k (h ≫ k) rfl L)
    ((Scheme.Modules.pullback f).mapIso ((Scheme.Modules.pullback g).mapIso α))
    ((Scheme.Modules.pullback h).mapIso ((Scheme.Modules.pullback k).mapIso α))
    ((Scheme.Modules.pullback (h ≫ k)).mapIso α)
    (Iso.ext (canHom_naturality f g (h ≫ k) w α.hom))
    (Iso.ext (canHom_naturality h k (h ≫ k) rfl α.hom))

/-- Pull back the specified boundary trivialization through its original commutative square. -/
def pullbackBoundaryTrivialization {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D) (w : f ≫ g = h ≫ k)
    (L : D.Modules)
    (τ : (Scheme.Modules.pullback g).obj L ≅ SheafOfModules.unit B.ringCatSheaf) :
    (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback k).obj L) ≅
      SheafOfModules.unit A.ringCatSheaf :=
  (pullbackSquareIso f g h k w L).symm ≪≫ (Scheme.Modules.pullback f).mapIso τ ≪≫
    Scheme.Modules.pullbackUnitIso f

private theorem frame_power_square_aux {D : Type*} [Category D]
    {Z P Q R H1 H2 T0 T1 U0 U1 U2 V0 V1 : D}
    (q : P ≅ Q) (s : Q ≅ R) (e : R ≅ V1)
    (pU : U0 ≅ U1) (v : U1 ≅ V1) (x : V1 ≅ V0) (u : U2 ≅ V0) (w : U0 ≅ U2)
    (g : Z ≅ P) (σ : Z ≅ H1) (k : H1 ≅ H2) (h : H2 ≅ R)
    (a : Z ≅ T0) (b : H1 ≅ T1) (τ : T0 ≅ U2) (σL : T0 ≅ T1)
    (hsquare : g ≪≫ q ≪≫ s = σ ≪≫ k ≪≫ h)
    (hunit : pU ≪≫ v ≪≫ x = w ≪≫ u) (hnat : a ≪≫ σL = σ ≪≫ b) :
    e = h.symm ≪≫ k.symm ≪≫ b ≪≫ σL.symm ≪≫ τ ≪≫ u ≪≫ x.symm ↔
      q ≪≫ s ≪≫ e ≪≫ v.symm ≪≫ pU.symm = g.symm ≪≫ a ≪≫ τ ≪≫ w.symm := by
  have hG : q ≪≫ s ≪≫ h.symm ≪≫ k.symm = g.symm ≪≫ σ := by
    simpa [Iso.trans_assoc] using
      congrArg (fun z => g.symm ≪≫ z ≪≫ h.symm ≪≫ k.symm) hsquare
  have hU : u ≪≫ x.symm ≪≫ v.symm ≪≫ pU.symm = w.symm := by
    simpa [Iso.trans_symm, Iso.trans_assoc] using congrArg (fun z => u ≪≫ z.symm) hunit
  have hN : σ ≪≫ b ≪≫ σL.symm = a := by
    simpa [Iso.trans_assoc] using congrArg (fun z => z ≪≫ σL.symm) hnat.symm
  have h1 := congrArg
    (fun z => z ≪≫ b ≪≫ σL.symm ≪≫ τ ≪≫ u ≪≫ x.symm ≪≫ v.symm ≪≫ pU.symm) hG
  have h2 := congrArg
    (fun z => g.symm ≪≫ z ≪≫ τ ≪≫ u ≪≫ x.symm ≪≫ v.symm ≪≫ pU.symm) hN
  have h3 := congrArg (fun z => g.symm ≪≫ a ≪≫ τ ≪≫ z) hU
  simp only [Iso.trans_assoc] at h1 h2
  have hc := h1.trans (h2.trans h3)
  constructor
  · intro he
    simpa only [he, Iso.trans_assoc] using hc
  · intro he
    simpa [Iso.trans_assoc] using
      congrArg (fun z => s.symm ≪≫ q.symm ≪≫ z ≪≫ pU ≪≫ v) (he.trans hc.symm)

private theorem map_inverse_root {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C' E H : C} (a : B ≅ A) (b : B ≅ C') (c : C' ≅ E) (d : H ≅ E) :
    F.mapIso (a.symm ≪≫ b ≪≫ c ≪≫ d.symm) =
      (F.mapIso a).symm ≪≫ F.mapIso b ≪≫ F.mapIso c ≪≫ (F.mapIso d).symm := by
  simp

private theorem nested_root_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C' : C} {P Q R U V : D} (a : A ≅ B) (b : A ≅ C') (c : F.obj B ≅ P)
    (d : Q ≅ F.obj C') (t : Q ≅ R) (u : R ≅ U) (x : V ≅ U) :
    c.symm ≪≫ F.mapIso (a.symm ≪≫ b) ≪≫ (d.symm ≪≫ t ≪≫ u) ≪≫ x.symm =
      c.symm ≪≫ (F.mapIso a).symm ≪≫ F.mapIso b ≪≫ d.symm ≪≫ t ≪≫ u ≪≫ x.symm := by
  simp [Iso.trans_assoc]

private theorem normalize_frame_power_aux {D : Type*} [Category D]
    {P Q R S T U : D} (a : P ≅ Q) (p : U ≅ T) (s : Q ≅ R) (e : R ≅ S)
    (v : T ≅ S) (z : Q ≅ T) (hz : z = s ≪≫ e ≪≫ v.symm) :
    a ≪≫ z ≪≫ p.symm = a ≪≫ s ≪≫ e ≪≫ v.symm ≪≫ p.symm := by
  simp only [hz, Iso.trans_assoc]

local instance (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)

local instance (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property X.unitModule :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
        ((Scheme.Modules.pullback f).obj Y.unitModule) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom _
    inferInstance

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      ((Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf)) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom _
    inferInstance

/-- The original root-frame equation after pullback through the entire boundary square is
exactly the canonical power equation used by full-boundary frame descent. -/
theorem boundary_root_frame_pullback_iff {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D) (w : f ≫ g = h ≫ k)
    (M L : D.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible D.toRingedSpace.presheaf
      (structureSheafRing D.toRingedSpace).property M] (n : ℕ)
    (α : tensorPower D.toRingedSpace.presheaf (structureSheafRing D.toRingedSpace).property
      M (n : ℤ) ≅ L)
    (τ : (Scheme.Modules.pullback g).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (e : (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback k).obj M) ≅
      SheafOfModules.unit A.ringCatSheaf) :
    (tensorPowerCongr A.toRingedSpace.presheaf (structureSheafRing A.toRingedSpace).property
        _ _ e n = boundaryRootPowerIso h ((Scheme.Modules.pullback k).obj M)
          ((Scheme.Modules.pullback k).obj L) n
          ((Scheme.Modules.pullbackTensorPowerIso k M n).symm ≪≫
            (Scheme.Modules.pullback k).mapIso α)
          (pullbackBoundaryTrivialization f g h k w L τ)) ↔
      pullbackPowerIso f ((Scheme.Modules.pullback g).obj M)
        (SheafOfModules.unit B.ringCatSheaf) (framePullbackIso f g h k w M e) n =
          (Scheme.Modules.pullback f).mapIso (boundaryRootPowerIso g M L n α τ) := by
  let S := pullbackSquareIso f g h k w M
  let u := Scheme.Modules.pullbackUnitIso f
  have hp1 := tensorPowerCongr_trans A.toRingedSpace.presheaf
    (structureSheafRing A.toRingedSpace).property S (e ≪≫ u.symm) n
  have hp2 := tensorPowerCongr_trans A.toRingedSpace.presheaf
    (structureSheafRing A.toRingedSpace).property e u.symm n
  have hp3 := tensorPowerCongr_symm A.toRingedSpace.presheaf
    (structureSheafRing A.toRingedSpace).property u n
  have hp := hp1.trans (congrArg (fun z => tensorPowerCongr A.toRingedSpace.presheaf
    (structureSheafRing A.toRingedSpace).property _ _ S n ≪≫ z)
      (hp2.trans (congrArg (fun z => tensorPowerCongr A.toRingedSpace.presheaf
        (structureSheafRing A.toRingedSpace).property _ _ e n ≪≫ z) hp3)))
  have hnorm := normalize_frame_power_aux
    (Scheme.Modules.pullbackTensorPowerIso f ((Scheme.Modules.pullback g).obj M) n)
    (Scheme.Modules.pullbackTensorPowerIso f (SheafOfModules.unit B.ringCatSheaf) n)
    _ _ _ _ hp
  have hroot := nested_root_eq (Scheme.Modules.pullback h)
    (Scheme.Modules.pullbackTensorPowerIso k M n) ((Scheme.Modules.pullback k).mapIso α)
    (Scheme.Modules.pullbackTensorPowerIso h ((Scheme.Modules.pullback k).obj M) n)
    (pullbackSquareIso f g h k w L) ((Scheme.Modules.pullback f).mapIso τ) u
    (structureSheafTensorPowerIso A n)
  have hrhs := map_inverse_root (Scheme.Modules.pullback f)
    (Scheme.Modules.pullbackTensorPowerIso g M n) ((Scheme.Modules.pullback g).mapIso α)
    τ (structureSheafTensorPowerIso B n)
  have hc := frame_power_square_aux
    (Scheme.Modules.pullbackTensorPowerIso f ((Scheme.Modules.pullback g).obj M) n)
    (tensorPowerCongr A.toRingedSpace.presheaf (structureSheafRing A.toRingedSpace).property
      _ _ S n)
    (tensorPowerCongr A.toRingedSpace.presheaf (structureSheafRing A.toRingedSpace).property
      _ _ e n)
    (Scheme.Modules.pullbackTensorPowerIso f (SheafOfModules.unit B.ringCatSheaf) n)
    (tensorPowerCongr A.toRingedSpace.presheaf (structureSheafRing A.toRingedSpace).property
      _ _ u n) (structureSheafTensorPowerIso A n) u
    ((Scheme.Modules.pullback f).mapIso (structureSheafTensorPowerIso B n))
    ((Scheme.Modules.pullback f).mapIso (Scheme.Modules.pullbackTensorPowerIso g M n))
    (pullbackSquareIso f g h k w (tensorPower D.toRingedSpace.presheaf
      (structureSheafRing D.toRingedSpace).property M (n : ℤ)))
    ((Scheme.Modules.pullback h).mapIso (Scheme.Modules.pullbackTensorPowerIso k M n))
    (Scheme.Modules.pullbackTensorPowerIso h ((Scheme.Modules.pullback k).obj M) n)
    ((Scheme.Modules.pullback f).mapIso ((Scheme.Modules.pullback g).mapIso α))
    ((Scheme.Modules.pullback h).mapIso ((Scheme.Modules.pullback k).mapIso α))
    ((Scheme.Modules.pullback f).mapIso τ) (pullbackSquareIso f g h k w L)
    (pullbackSquareIso_tensorPower f g h k w M n)
    (Scheme.Modules.pullbackTensorPowerIso_structureSheaf f n)
    (pullbackSquareIso_naturality f g h k w α)
  constructor
  · intro he
    exact hnorm.trans ((hc.mp (he.trans hroot)).trans hrhs.symm)
  · intro he
    exact (hc.mpr (hnorm.symm.trans (he.trans hrhs))).trans hroot.symm


universe v

set_option maxHeartbeats 600000 in
-- The root and frame equations live in three different scheme-module categories.
/-- A frame given only on the full limit boundary descends compatibly with the specified
root and original boundary trivialization, together with all specified finite linear equations.
The original root module is preserved under the single resulting transition. -/
theorem exists_boundary_root_frame_comp_eq_of_isLimit_finite
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (B C : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
    (b : B ⟶ C) (cB : Limits.Cone B) (hcB : Limits.IsLimit cB)
    [∀ i, CompactSpace (B.obj i)] [∀ i, QuasiSeparatedSpace (B.obj i)]
    (cC : Limits.Cone C) (bLim : cB.pt ⟶ cC.pt)
    (hb : ∀ i, cB.π.app i ≫ b.app i = bLim ≫ cC.π.app i)
    (i : I) (M L : (C.obj i).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj i).toRingedSpace.presheaf
      (structureSheafRing (C.obj i).toRingedSpace).property M] (n : ℕ)
    (α : tensorPower (C.obj i).toRingedSpace.presheaf
      (structureSheafRing (C.obj i).toRingedSpace).property M (n : ℤ) ≅ L)
    (τ : (Scheme.Modules.pullback (b.app i)).obj L ≅
      SheafOfModules.unit (B.obj i).ringCatSheaf)
    (eLim : (Scheme.Modules.pullback bLim).obj
      ((Scheme.Modules.pullback (cC.π.app i)).obj M) ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    (heLim : tensorPowerCongr cB.pt.toRingedSpace.presheaf
      (structureSheafRing cB.pt.toRingedSpace).property _ _ eLim n =
        boundaryRootPowerIso bLim ((Scheme.Modules.pullback (cC.π.app i)).obj M)
          ((Scheme.Modules.pullback (cC.π.app i)).obj L) n
          ((Scheme.Modules.pullbackTensorPowerIso (cC.π.app i) M n).symm ≪≫
            (Scheme.Modules.pullback (cC.π.app i)).mapIso α)
          (pullbackBoundaryTrivialization (cB.π.app i) (b.app i) bLim
            (cC.π.app i) (hb i) L τ)) :
    let A := (Scheme.Modules.pullback (b.app i)).obj M
    let U := SheafOfModules.unit (B.obj i).ringCatSheaf
    let N := framePullbackIso (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M eLim
    ∀ {η : Type v} [Finite η] (P : η → (B.obj i).Modules)
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
        (tensorPowerCongr (B.obj j).toRingedSpace.presheaf
          (structureSheafRing (B.obj j).toRingedSpace).property _ _ e n =
            boundaryRootPowerIso (b.app j) ((Scheme.Modules.pullback (C.map f)).obj M)
              ((Scheme.Modules.pullback (C.map f)).obj L) n
              ((Scheme.Modules.pullbackTensorPowerIso (C.map f) M n).symm ≪≫
                (Scheme.Modules.pullback (C.map f)).mapIso α)
              (pullbackBoundaryTrivialization (B.map f) (b.app i) (b.app j) (C.map f)
                (b.naturality f) L τ)) ∧
        ∀ x, (Scheme.Modules.pullback (B.map f)).map (s x) ≫ m.hom =
          (Scheme.Modules.pullback (B.map f)).map (t x) := by
  dsimp only
  intro η _ P _ s t hst
  have hα := (boundary_root_frame_pullback_iff (cB.π.app i) (b.app i) bLim
    (cC.π.app i) (hb i) M L n α τ eLim).mp heLim
  obtain ⟨j, f, e, he, hpow, hst'⟩ :=
    exists_boundary_frame_power_comp_eq_of_isLimit_finite B C b cB hcB cC bLim hb i M eLim
      (fun _ : Unit => n) (fun _ => (boundaryRootPowerIso (b.app i) M L n α τ).hom)
      (fun _ => congrArg Iso.hom hα) P s t hst
  refine ⟨j, f, e, he, ?_, hst'⟩
  exact (boundary_root_frame_pullback_iff (B.map f) (b.app i) (b.app j) (C.map f)
    (b.naturality f) M L n α τ e).mpr (Iso.ext (hpow ()))

end Stacks.AlgebraicGeometry.ModuleLimits
