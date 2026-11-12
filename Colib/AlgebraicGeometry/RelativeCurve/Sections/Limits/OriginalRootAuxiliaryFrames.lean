/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.Invertible.LimitBoundaryRoot
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.DirectRootAuxiliaryFrames
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.AuxiliaryNumeratorDescentEquation
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.BoundaryScalarPullback

/-! # The original root, auxiliary pair and frames at a common stage

The actual root is selected first. The original auxiliary module and both sections
are then descended after that root. Its prescribed-refinement frame consumer makes
one further stage satisfy the original power and both boundary-one equations.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules
open Stacks.SheafOfModules.Invertible
universe u
namespace Stacks.AlgebraicGeometry.ModuleLimits

private theorem original_refined_frame {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B E : C} {U : D} (e : A ≅ B) (c : E ≅ B) (t : F.obj A ≅ U) :
    F.mapIso c ≪≫ F.mapIso e.symm ≪≫ t = (F.mapIso (e ≪≫ c.symm)).symm ≪≫ t := by
  simp only [Functor.mapIso_trans, Iso.trans_symm, Iso.symm_symm_eq,
    Functor.mapIso_symm, Iso.trans_assoc]

local instance instOriginalRootAuxiliaryFramesInvertiblePullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L hL

set_option maxHeartbeats 800000 in
-- The existential package retains the actual original root and three stage comparisons.
/-- Descend the original root, auxiliary sections and full-boundary frames to a
common refinement without reselecting the root after the pair has been chosen. -/
theorem exists_original_root_auxiliaryFrames_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (B C : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (C.map f)]
    (b : B ⟶ C) (cB : Cone B) (hcB : IsLimit cB)
    [∀ i, CompactSpace (B.obj i)] [∀ i, QuasiSeparatedSpace (B.obj i)]
    (cC : Cone C) (hcC : IsLimit cC)
    [∀ i, CompactSpace (C.obj i)] [∀ i, QuasiSeparatedSpace (C.obj i)]
    (bLim : cB.pt ⟶ cC.pt)
    (hb : ∀ i, cB.π.app i ≫ b.app i = bLim ≫ cC.π.app i)
    (i : I) (L : (C.obj i).Modules) [L.IsFinitePresentation]
    (τ : (Scheme.Modules.pullback (b.app i)).obj L ≅
      SheafOfModules.unit (B.obj i).ringCatSheaf)
    (M : cC.pt.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible cC.pt.toRingedSpace.presheaf
      (structureSheafRing cC.pt.toRingedSpace).property M] (n : ℕ)
    (α : tensorPower cC.pt.toRingedSpace.presheaf
      (structureSheafRing cC.pt.toRingedSpace).property M (n : ℤ) ≅
        (Scheme.Modules.pullback (cC.π.app i)).obj L)
    (e₀ : (Scheme.Modules.pullback bLim).obj M ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    (he₀ : tensorPowerCongr cB.pt.toRingedSpace.presheaf
      (structureSheafRing cB.pt.toRingedSpace).property _ _ e₀ n =
        boundaryRootPowerIso bLim M ((Scheme.Modules.pullback (cC.π.app i)).obj L) n α
          (pullbackBoundaryTrivialization (cB.π.app i) (b.app i) bLim
            (cC.π.app i) (hb i) L τ))
    (N₀ : cC.pt.Modules)
    (hN₀ : AlgebraicGeometry.SheafOfModules.IsInvertible cC.pt.sheaf.obj
      cC.pt.ringCatSheaf.property N₀)
    (a₀ : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor cC.pt.sheaf).obj M).obj N₀, ⊤))
    (b₀ : Γ(N₀, ⊤))
    (eN₀ : (Scheme.Modules.pullback bLim).obj N₀ ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    (hb₀ : Hom.app eN₀.hom ⊤ (pullbackGlobalSections bLim N₀ b₀) = (1 : Γ(cB.pt, ⊤)))
    (ha₀ : Hom.app (Scheme.Modules.pullbackTensorFrame bLim M N₀ e₀ eN₀).hom ⊤
      (pullbackGlobalSections bLim _ a₀) = (1 : Γ(cB.pt, ⊤))) :
    ∃ (k : I) (e : k ⟶ i) (Mk : (C.obj k).Modules)
      (hMk : AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj k).toRingedSpace.presheaf
        (structureSheafRing (C.obj k).toRingedSpace).property Mk),
      let _ := hMk
      ∃ (eM : M ≅ (Scheme.Modules.pullback (cC.π.app k)).obj Mk) (j : I) (f : j ⟶ k)
        (β : tensorPower (C.obj j).toRingedSpace.presheaf
          (structureSheafRing (C.obj j).toRingedSpace).property
            ((Scheme.Modules.pullback (C.map f)).obj Mk) (n : ℤ) ≅
          (Scheme.Modules.pullback (C.map f)).obj
            ((Scheme.Modules.pullback (C.map e)).obj L)),
      let Mj := (Scheme.Modules.pullback (C.map f)).obj Mk
  let _ : AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj j).sheaf.obj
      (C.obj j).ringCatSheaf.property Mj :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      (C.map f).toLRSHom.toShHom Mk hMk
      let Qk := (Scheme.Modules.pullback (C.map e)).obj L
      let Qj := (Scheme.Modules.pullback (C.map f)).obj Qk
      let eMj := eM ≪≫ (canIso (cC.π.app j) (C.map f) (cC.π.app k) (cC.w f) Mk).symm
      let eL := canIso (cC.π.app j) (C.map f) (cC.π.app k) (cC.w f) Qk ≪≫
        canIso (cC.π.app k) (C.map e) (cC.π.app i) (cC.w e) L
      let τk := pullbackBoundaryTrivialization (B.map e) (b.app i) (b.app k) (C.map e)
        (b.naturality e) L τ
      let τj := pullbackBoundaryTrivialization (B.map f) (b.app k) (b.app j) (C.map f)
        (b.naturality f) Qk τk
      let αj := (Scheme.Modules.pullbackTensorPowerIso (cC.π.app j) Mj n).symm ≪≫
        (Scheme.Modules.pullback (cC.π.app j)).mapIso β
      let eLim := (Scheme.Modules.pullback bLim).mapIso eMj.symm ≪≫ e₀
      (tensorPowerCongr cC.pt.toRingedSpace.presheaf
        (structureSheafRing cC.pt.toRingedSpace).property _ _ eMj n ≪≫ αj ≪≫ eL = α) ∧
      (tensorPowerCongr cB.pt.toRingedSpace.presheaf
        (structureSheafRing cB.pt.toRingedSpace).property _ _ eLim n =
        boundaryRootPowerIso bLim ((Scheme.Modules.pullback (cC.π.app j)).obj Mj)
          ((Scheme.Modules.pullback (cC.π.app j)).obj Qj) n αj
          (pullbackBoundaryTrivialization (cB.π.app j) (b.app j) bLim
            (cC.π.app j) (hb j) Qj τj)) ∧
      ∃ (j' : I) (g : j' ⟶ j) (Nj : (C.obj j').Modules)
        (_hNj : AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj j').sheaf.obj
          (C.obj j').ringCatSheaf.property Nj)
        (F : N₀ ≅ (Scheme.Modules.pullback (cC.π.app j')).obj Nj)
        (eAux : (Scheme.Modules.pullback (b.app j')).obj Nj ≅
          SheafOfModules.unit (B.obj j').ringCatSheaf)
        (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor (C.obj j').sheaf).obj
          ((Scheme.Modules.pullback (C.map g)).obj Mj)).obj Nj, ⊤)) (bN : Γ(Nj, ⊤)),
      let ER := Scheme.Modules.refinedSectionModelIso (cC.π.app j') (C.map g)
        (cC.π.app j) (cC.w g) Mj eMj
      let Mj' := (Scheme.Modules.pullback (C.map g)).obj Mj
      let Qj' := (Scheme.Modules.pullback (C.map g)).obj Qj
      let β' := (Scheme.Modules.pullbackTensorPowerIso (C.map g) Mj n).symm ≪≫
        (Scheme.Modules.pullback (C.map g)).mapIso β
      let τj' := pullbackBoundaryTrivialization (B.map g) (b.app j) (b.app j') (C.map g)
        (b.naturality g) Qj τj
      let eLim' := (Scheme.Modules.pullback bLim).mapIso
        (canIso (cC.π.app j') (C.map g) (cC.π.app j) (cC.w g) Mj) ≪≫ eLim
      Hom.app
        (tensorProductIso cC.pt.sheaf.obj cC.pt.ringCatSheaf.property ER F ≪≫
          (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (cC.π.app j') Mj' Nj).symm).hom
        ⊤ a₀ = pullbackGlobalSections (cC.π.app j') _ a ∧
      Hom.app F.hom ⊤ b₀ = pullbackGlobalSections (cC.π.app j') Nj bN ∧
      pullbackBoundaryTrivialization (cB.π.app j') (b.app j') bLim (cC.π.app j') (hb j') Nj eAux =
        ((Scheme.Modules.pullback bLim).mapIso F).symm ≪≫ eN₀ ∧
      Hom.app eAux.hom ⊤ (pullbackGlobalSections (b.app j') Nj bN) = (1 : Γ(B.obj j', ⊤)) ∧
      ∃ (ℓ : I) (h : ℓ ⟶ j')
        (eB : (Scheme.Modules.pullback (b.app ℓ)).obj
          ((Scheme.Modules.pullback (C.map h)).obj Mj') ≅
            SheafOfModules.unit (B.obj ℓ).ringCatSheaf),
      let m := framePullbackIso (B.map h) (b.app j') (b.app ℓ) (C.map h)
        (b.naturality h) Mj' eB
      ((Scheme.Modules.pullback (cB.π.app ℓ)).map m.hom ≫
          canHom (cB.π.app ℓ) (B.map h) (cB.π.app j') (cB.w h)
            (SheafOfModules.unit (B.obj j').ringCatSheaf) =
        canHom (cB.π.app ℓ) (B.map h) (cB.π.app j') (cB.w h)
          ((Scheme.Modules.pullback (b.app j')).obj Mj') ≫
            (framePullbackIso (cB.π.app j') (b.app j') bLim (cC.π.app j') (hb j') Mj' eLim').hom) ∧
      (tensorPowerCongr (B.obj ℓ).toRingedSpace.presheaf
        (structureSheafRing (B.obj ℓ).toRingedSpace).property _ _ eB n =
        boundaryRootPowerIso (b.app ℓ) ((Scheme.Modules.pullback (C.map h)).obj Mj')
          ((Scheme.Modules.pullback (C.map h)).obj Qj') n
          ((Scheme.Modules.pullbackTensorPowerIso (C.map h) Mj' n).symm ≪≫
            (Scheme.Modules.pullback (C.map h)).mapIso β')
          (pullbackBoundaryTrivialization (B.map h) (b.app j') (b.app ℓ) (C.map h)
            (b.naturality h) Qj' τj')) ∧
      Hom.app
        ((Scheme.Modules.pullback (b.app ℓ)).mapIso
            (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (C.map h) Mj' Nj) ≪≫
          Scheme.Modules.pullbackTensorFrame (b.app ℓ)
            ((Scheme.Modules.pullback (C.map h)).obj Mj')
            ((Scheme.Modules.pullback (C.map h)).obj Nj) eB
            (pullbackBoundaryTrivialization (B.map h) (b.app j') (b.app ℓ) (C.map h)
              (b.naturality h) Nj eAux)).hom ⊤
        (pullbackGlobalSections (b.app ℓ) _ (pullbackGlobalSections (C.map h) _ a)) =
          (1 : Γ(B.obj ℓ, ⊤)) ∧
      Hom.app
        (pullbackBoundaryTrivialization (B.map h) (b.app j') (b.app ℓ) (C.map h)
          (b.naturality h) Nj eAux).hom ⊤
        (pullbackGlobalSections (b.app ℓ) _ (pullbackGlobalSections (C.map h) Nj bN)) =
          (1 : Γ(B.obj ℓ, ⊤)) := by
  obtain ⟨k, e, Mk, hMk, eM, j, f, β, hrec, hroot, hall⟩ :=
    exists_root_boundary_frame_of_isLimit_finite B C b cB hcB cC hcC bLim hb i L τ M n α e₀ he₀
  let := hMk
  let Mj := (Scheme.Modules.pullback (C.map f)).obj Mk
  let _ : AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj j).sheaf.obj
      (C.obj j).ringCatSheaf.property Mj :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      (C.map f).toLRSHom.toShHom Mk hMk
  let eMj := eM ≪≫ (canIso (cC.π.app j) (C.map f) (cC.π.app k) (cC.w f) Mk).symm
  obtain ⟨j', g, Nj, hNj, F, eAux, a, bN, ha, hbrecover, hAux, hbN⟩ :=
    Scheme.Modules.exists_directRoot_auxiliaryFrames_of_isLimit B C cC hcC b cB hcB bLim hb
      j Mj M N₀ eMj hN₀ a₀ b₀ eN₀ hb₀
  let ER := Scheme.Modules.refinedSectionModelIso (cC.π.app j') (C.map g)
    (cC.π.app j) (cC.w g) Mj eMj
  let Mj' := (Scheme.Modules.pullback (C.map g)).obj Mj
  let P (_ : PUnit.{1}) := SheafOfModules.unit (B.obj j').ringCatSheaf
  let (_ : PUnit.{1}) : (P PUnit.unit).IsFinitePresentation := isFinitePresentation_unit (B.obj j')
  let s (_ : PUnit.{1}) := Scheme.Modules.auxiliaryBoundaryNumerator (b.app j') Mj' Nj eAux a
  let t (_ : PUnit.{1}) := unitHomEquivTop (SheafOfModules.unit (B.obj j').ringCatSheaf)
    (1 : Γ(B.obj j', ⊤))
  have hn := original_refined_frame (Scheme.Modules.pullback bLim) eMj
    (canIso (cC.π.app j') (C.map g) (cC.π.app j) (cC.w g) Mj) e₀
  have hs (x : PUnit.{1}) :
      (Scheme.Modules.pullback (cB.π.app j')).map (s x) ≫
        (framePullbackIso (cB.π.app j') (b.app j') bLim (cC.π.app j') (hb j') Mj'
          ((Scheme.Modules.pullback bLim).mapIso
            (canIso (cC.π.app j') (C.map g) (cC.π.app j) (cC.w g) Mj) ≪≫
              (Scheme.Modules.pullback bLim).mapIso eMj.symm ≪≫ e₀)).hom =
      (Scheme.Modules.pullback (cB.π.app j')).map (t x) := by
    rw [hn]
    exact (Scheme.Modules.auxiliaryBoundaryNumerator_original_one_iff
      (cB.π.app j') (b.app j') bLim (cC.π.app j') (hb j') Mj' Nj M N₀ ER F e₀ eN₀ eAux hAux
      a₀ a ha).mpr ha₀
  obtain ⟨ℓ, h, eB, he, hpow, hst⟩ := hall j' g P s t hs
  refine ⟨k, e, Mk, hMk, eM, j, f, β, hrec, hroot, j', g, Nj, hNj, F, eAux, a, bN,
    ha, hbrecover, hAux, hbN, ℓ, h, eB, he, hpow, ?_, ?_⟩
  · exact (Scheme.Modules.auxiliaryBoundaryNumerator_pullback_one_iff
      (B.map h) (b.app j') (b.app ℓ) (C.map h) (b.naturality h) Mj' Nj eAux eB a).mp
        (hst PUnit.unit)
  · exact Scheme.Modules.pullbackBoundaryTrivialization_section_one
      (B.map h) (b.app j') (b.app ℓ) (C.map h) (b.naturality h) Nj eAux bN hbN

end Stacks.AlgebraicGeometry.ModuleLimits
