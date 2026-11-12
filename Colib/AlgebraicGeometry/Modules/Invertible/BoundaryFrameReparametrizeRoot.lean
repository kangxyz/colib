/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Modules.Invertible.BoundaryFrameReparametrize
public import Colib.AlgebraicGeometry.Modules.Invertible.BoundaryRootPullback

/-! # The original root equation under boundary reparametrization

Only the boundary frames move. The ambient root, target and power isomorphism
remain exactly the original objects, without an identity ambient pullback.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.SheafOfModules.Invertible
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace AlgebraicGeometry.Scheme.Modules

local instance reparamRootPullbackInvertible {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((pullback f).obj M) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom M hM

local instance reparamRootUnitInvertible (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)

local instance reparamRootPullbackUnitStacks {A B : Scheme.{u}} (u : A ⟶ B) :
    Stacks.SheafOfModules.IsInvertible A.presheaf (ringSheafCond A)
      ((pullback u).obj (SheafOfModules.unit B.ringCatSheaf)) :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      u.toLRSHom.toShHom _ (reparamRootUnitInvertible B))

/-- The original natural-power root equation is preserved with its exact original
ambient root and power isomorphism, under any prescribed boundary reparametrization. -/
theorem boundaryFrameReparametrize_root {A B X : Scheme.{u}}
    (u : A ⟶ B) (g : B ⟶ X) (h : A ⟶ X) (w : u ≫ g = h)
    (M L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M] (n : ℕ)
    (α : tensorPower X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
      M (n : ℤ) ≅ L)
    (τ : (pullback g).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (e : (pullback g).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (he : tensorPowerCongr B.presheaf (ringSheafCond B) _ _ e n =
      boundaryRootPowerIso g M L n α τ) :
    tensorPowerCongr A.presheaf (ringSheafCond A) _ _
      (boundaryFrameReparametrize u g h w M e) n =
    boundaryRootPowerIso h M L n α (boundaryFrameReparametrize u g h w L τ) := by
  let cM := canIso u g h w M
  let cL := canIso u g h w L
  let cP := canIso u g h w (tensorPower X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property M (n : ℤ))
  let qg := pullbackTensorPowerIso g M n
  let qh := pullbackTensorPowerIso h M n
  let tM := pullbackTensorPowerIso u ((pullback g).obj M) n
  let tU := pullbackTensorPowerIso u (SheafOfModules.unit B.ringCatSheaf) n
  let pc := tensorPowerCongr A.presheaf (ringSheafCond A) _ _ cM n
  let pe := tensorPowerCongr A.presheaf (ringSheafCond A) _ _ ((pullback u).mapIso e) n
  let pu := tensorPowerCongr A.presheaf (ringSheafCond A) _ _ (pullbackUnitIso u) n
  let pB := tensorPowerCongr B.presheaf (ringSheafCond B) _ _ e n
  let sB := structureSheafTensorPowerIso B n
  let sA := structureSheafTensorPowerIso A n
  have hn : pe = tM.symm ≪≫ (pullback u).mapIso pB ≪≫ tU := by
    have H := congrArg (fun z => tM.symm ≪≫ z)
      (pullbackTensorPowerIso_naturality u e n)
    simpa only [tM, pe, pB, tU, Iso.trans_assoc, Iso.symm_self_id_assoc] using H.symm
  have hu : tU ≪≫ pu = (pullback u).mapIso sB ≪≫ pullbackUnitIso u ≪≫ sA.symm := by
    have H := congrArg (fun z => z ≪≫ sA.symm)
      (pullbackTensorPowerIso_structureSheaf u n)
    simpa only [tU, pu, sA, sB, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using H
  have hc : pc.symm ≪≫ tM.symm ≪≫ ((pullback u).mapIso qg).symm = qh.symm ≪≫ cP.symm := by
    have H := congrArg (fun z => cP ≪≫ z) (pullbackTensorPowerIso_can u g h w M n)
    have H' : (pullback u).mapIso qg ≪≫ tM ≪≫ pc = cP ≪≫ qh := by
      simpa only [cP, qg, tM, pc, cM, qh, Iso.trans_assoc, Iso.self_symm_id_assoc] using H
    have H'' := congrArg Iso.symm H'
    simpa only [Iso.trans_symm, Iso.trans_assoc] using H''
  have hα : cP.symm ≪≫ (pullback u).mapIso ((pullback g).mapIso α) =
      (pullback h).mapIso α ≪≫ cL.symm := by
    have H : (pullback u).mapIso ((pullback g).mapIso α) ≪≫ cL =
        cP ≪≫ (pullback h).mapIso α :=
      Iso.ext (canHom_naturality u g h w α.hom)
    have H' := congrArg (fun z => cP.symm ≪≫ z ≪≫ cL.symm) H
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl,
      Iso.symm_self_id_assoc] using H'
  have hstart : tensorPowerCongr A.presheaf (ringSheafCond A) _ _
      (boundaryFrameReparametrize u g h w M e) n = pc.symm ≪≫ pe ≪≫ pu := by
    have hp1 := tensorPowerCongr_trans A.toRingedSpace.presheaf
      (structureSheafRing A.toRingedSpace).property cM.symm
      ((pullback u).mapIso e ≪≫ pullbackUnitIso u) n
    have hp2 := tensorPowerCongr_trans A.toRingedSpace.presheaf
      (structureSheafRing A.toRingedSpace).property
      ((pullback u).mapIso e) (pullbackUnitIso u) n
    have hp3 := tensorPowerCongr_symm A.toRingedSpace.presheaf
      (structureSheafRing A.toRingedSpace).property cM n
    have H := hp1.trans (congrArg (fun z =>
      tensorPowerCongr A.toRingedSpace.presheaf
        (structureSheafRing A.toRingedSpace).property _ _ cM.symm n ≪≫ z) hp2)
    exact H.trans (congrArg (fun z => z ≪≫ pe ≪≫ pu) hp3)
  have hmid : pc.symm ≪≫ pe ≪≫ pu =
      pc.symm ≪≫ tM.symm ≪≫ (pullback u).mapIso pB ≪≫
        (pullback u).mapIso sB ≪≫ pullbackUnitIso u ≪≫ sA.symm := by
    rw [hn]
    simpa only [Iso.trans_assoc] using
      congrArg (fun z => pc.symm ≪≫ tM.symm ≪≫ (pullback u).mapIso pB ≪≫ z) hu
  have hframe : (pullback u).mapIso pB ≪≫ (pullback u).mapIso sB =
      ((pullback u).mapIso qg).symm ≪≫
        (pullback u).mapIso ((pullback g).mapIso α) ≪≫ (pullback u).mapIso τ := by
    have H := congrArg (fun z => (pullback u).mapIso z ≪≫ (pullback u).mapIso sB) he
    simpa only [pB, sB, qg, boundaryRootPowerIso, Functor.mapIso_trans, Functor.mapIso_symm,
      Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl] using H
  have hmid' := congrArg (fun z => pc.symm ≪≫ tM.symm ≪≫ z ≪≫
    pullbackUnitIso u ≪≫ sA.symm) hframe
  have hend := congrArg (fun z => z ≪≫
    (pullback u).mapIso ((pullback g).mapIso α) ≪≫ (pullback u).mapIso τ ≪≫
      pullbackUnitIso u ≪≫ sA.symm) hc
  have htarget := congrArg (fun z => qh.symm ≪≫ z ≪≫ (pullback u).mapIso τ ≪≫
    pullbackUnitIso u ≪≫ sA.symm) hα
  calc
    _ = pc.symm ≪≫ pe ≪≫ pu := hstart
    _ = pc.symm ≪≫ tM.symm ≪≫ (pullback u).mapIso pB ≪≫
        (pullback u).mapIso sB ≪≫ pullbackUnitIso u ≪≫ sA.symm := hmid
    _ = pc.symm ≪≫ tM.symm ≪≫ ((pullback u).mapIso qg).symm ≪≫
        (pullback u).mapIso ((pullback g).mapIso α) ≪≫
        (pullback u).mapIso τ ≪≫ pullbackUnitIso u ≪≫ sA.symm := by
      simpa only [Iso.trans_assoc] using hmid'
    _ = qh.symm ≪≫ cP.symm ≪≫
        (pullback u).mapIso ((pullback g).mapIso α) ≪≫
        (pullback u).mapIso τ ≪≫ pullbackUnitIso u ≪≫ sA.symm := by
      simpa only [Iso.trans_assoc] using hend
    _ = boundaryRootPowerIso h M L n α
        (boundaryFrameReparametrize u g h w L τ) := by
      simpa only [boundaryRootPowerIso, boundaryFrameReparametrize, qh, cP, cL, sA,
        Iso.trans_assoc] using htarget

end AlgebraicGeometry.Scheme.Modules
