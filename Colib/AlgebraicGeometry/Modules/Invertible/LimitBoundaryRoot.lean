/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryRootRefinement

/-!
# Descent of a specified root with its full-boundary frame

The invertible root is chosen internally by unconditional module descent. Its original power
isomorphism and full-boundary frame then descend with any finite family of linear equations.
The original cone comparisons and the original boundary trivialization are retained throughout.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Invertible

universe u v

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

private theorem reverse_root_recovery {D : Type*} [Category D] {A B C E : D}
    (e : A ≅ B) (β : B ≅ C) (l : C ≅ E) (α : A ≅ E)
    (h : e ≪≫ β ≪≫ l = α) : β ≪≫ l = e.symm ≪≫ α := by
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc] using
    congrArg (fun z => e.symm ≪≫ z) h

private theorem map_iso_comp_tail {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C' : C} {U : D} (a : A ≅ B) (b : B ≅ C') (t : F.obj C' ≅ U) :
    F.mapIso a ≪≫ F.mapIso b ≪≫ t = F.mapIso (a ≪≫ b) ≪≫ t := by
  rw [F.mapIso_trans, Iso.trans_assoc]

set_option maxHeartbeats 600000 in
-- The original root and both cone squares involve several iterated module categories.
/-- A specified invertible root and its original full-boundary frame admit a common stage.
The root is selected before the finite equations. After any prescribed refinement, every such
family is satisfied by one actual frame on a further stage of that same root, with its power
equation and recovery.
The result assumes neither a stage root nor a stage frame. -/
@[colib_tag "COL-1112", colib_ref "axiom_stacks_5ed82d14"
  "AlgebraicGeometry/ModuleLimits/InvertibleUnconditional.lean:191-203"
  "ingredient" "Choose the actual invertible root before common-stage power and frame descent"]
theorem exists_root_boundary_frame_of_isLimit_finite
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
            (cC.π.app i) (hb i) L τ)) :
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
      ∀ (j' : I) (g : j' ⟶ j),
      let Mj' := (Scheme.Modules.pullback (C.map g)).obj Mj
      let Qj' := (Scheme.Modules.pullback (C.map g)).obj Qj
      let β' := (Scheme.Modules.pullbackTensorPowerIso (C.map g) Mj n).symm ≪≫
        (Scheme.Modules.pullback (C.map g)).mapIso β
      let τj' := pullbackBoundaryTrivialization (B.map g) (b.app j) (b.app j') (C.map g)
        (b.naturality g) Qj τj
      let eLim' := (Scheme.Modules.pullback bLim).mapIso
        (canIso (cC.π.app j') (C.map g) (cC.π.app j) (cC.w g) Mj) ≪≫ eLim
      let A := (Scheme.Modules.pullback (b.app j')).obj Mj'
      let U := SheafOfModules.unit (B.obj j').ringCatSheaf
      let N := framePullbackIso (cB.π.app j') (b.app j') bLim (cC.π.app j') (hb j') Mj' eLim'
      ∀ {η : Type v} [Finite η] (P : η → (B.obj j').Modules)
        [∀ x, (P x).IsFinitePresentation] (s : ∀ x, P x ⟶ A) (t : ∀ x, P x ⟶ U),
        (∀ x, (Scheme.Modules.pullback (cB.π.app j')).map (s x) ≫ N.hom =
          (Scheme.Modules.pullback (cB.π.app j')).map (t x)) →
        ∃ (ℓ : I) (h : ℓ ⟶ j')
          (eB : (Scheme.Modules.pullback (b.app ℓ)).obj
            ((Scheme.Modules.pullback (C.map h)).obj Mj') ≅
              SheafOfModules.unit (B.obj ℓ).ringCatSheaf),
          let m := framePullbackIso (B.map h) (b.app j') (b.app ℓ) (C.map h)
            (b.naturality h) Mj' eB
          ((Scheme.Modules.pullback (cB.π.app ℓ)).map m.hom ≫
              canHom (cB.π.app ℓ) (B.map h) (cB.π.app j') (cB.w h) U =
            canHom (cB.π.app ℓ) (B.map h) (cB.π.app j') (cB.w h) A ≫ N.hom) ∧
          (tensorPowerCongr (B.obj ℓ).toRingedSpace.presheaf
            (structureSheafRing (B.obj ℓ).toRingedSpace).property _ _ eB n =
              boundaryRootPowerIso (b.app ℓ) ((Scheme.Modules.pullback (C.map h)).obj Mj')
                ((Scheme.Modules.pullback (C.map h)).obj Qj') n
                ((Scheme.Modules.pullbackTensorPowerIso (C.map h) Mj' n).symm ≪≫
                  (Scheme.Modules.pullback (C.map h)).mapIso β')
                (pullbackBoundaryTrivialization (B.map h) (b.app j') (b.app ℓ) (C.map h)
                  (b.naturality h) Qj' τj')) ∧
          ∀ x, (Scheme.Modules.pullback (B.map h)).map (s x) ≫ m.hom =
            (Scheme.Modules.pullback (B.map h)).map (t x) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible cC.pt.sheaf.obj
      cC.pt.ringCatSheaf.property M := hM
  obtain ⟨k, e, Mk, hMk, eM, j, f, β, hβ⟩ :=
    exists_tensorPower_root_of_isLimit C cC hcC i L M n α
  have : AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj k).toRingedSpace.presheaf
      (structureSheafRing (C.obj k).toRingedSpace).property Mk := hMk
  let Mj := (Scheme.Modules.pullback (C.map f)).obj Mk
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
  have hrec : tensorPowerCongr cC.pt.toRingedSpace.presheaf
      (structureSheafRing cC.pt.toRingedSpace).property _ _ eMj n ≪≫ αj ≪≫ eL = α :=
    tensorPower_root_recovery (X := cC.pt) (Y := C.obj j) (Z := C.obj k)
      (cC.π.app j) (C.map f) (cC.π.app k) (cC.w f) Mk M _ Qj
      eM n α β eL (Iso.ext hβ)
  have hroot : αj ≪≫ eL = tensorPowerCongr cC.pt.toRingedSpace.presheaf
      (structureSheafRing cC.pt.toRingedSpace).property _ _ eMj.symm n ≪≫ α :=
    (reverse_root_recovery _ αj eL α hrec).trans (congrArg (fun z => z ≪≫ α)
      (tensorPowerCongr_symm cC.pt.toRingedSpace.presheaf
        (structureSheafRing cC.pt.toRingedSpace).property eMj n).symm)
  let τ₀ := pullbackBoundaryTrivialization (cB.π.app i) (b.app i) bLim
    (cC.π.app i) (hb i) L τ
  have hτk : pullbackBoundaryTrivialization (cB.π.app k) (b.app k) bLim
      (cC.π.app k) (hb k) Qk τk =
        (Scheme.Modules.pullback bLim).mapIso
          (canIso (cC.π.app k) (C.map e) (cC.π.app i) (cC.w e) L) ≪≫ τ₀ :=
    pullbackBoundaryTrivialization_comp (cB.π.app k) (B.map e) (cB.π.app i)
      bLim (b.app k) (b.app i) (cC.π.app k) (C.map e) (cC.π.app i)
      (cB.w e) (cC.w e) (hb k) (b.naturality e) (hb i) L τ
  have hτj := pullbackBoundaryTrivialization_comp (cB.π.app j) (B.map f) (cB.π.app k)
    bLim (b.app j) (b.app k) (cC.π.app j) (C.map f) (cC.π.app k)
    (cB.w f) (cC.w f) (hb j) (b.naturality f) (hb k) Qk τk
  have hτ : pullbackBoundaryTrivialization (cB.π.app j) (b.app j) bLim
      (cC.π.app j) (hb j) Qj τj = (Scheme.Modules.pullback bLim).mapIso eL ≪≫ τ₀ :=
    hτj.trans ((congrArg (fun z => (Scheme.Modules.pullback bLim).mapIso
      (canIso (cC.π.app j) (C.map f) (cC.π.app k) (cC.w f) Qk) ≪≫ z) hτk).trans
        (map_iso_comp_tail (Scheme.Modules.pullback bLim) _ _ τ₀))
  have hframe₀ := boundary_root_frame_transport (X := cB.pt) (Y := cC.pt) bLim
    _ M _ _ eMj.symm n αj α eL τ₀ e₀
    hroot he₀
  have hframe : tensorPowerCongr cB.pt.toRingedSpace.presheaf
      (structureSheafRing cB.pt.toRingedSpace).property _ _ eLim n =
        boundaryRootPowerIso bLim ((Scheme.Modules.pullback (cC.π.app j)).obj Mj)
          ((Scheme.Modules.pullback (cC.π.app j)).obj Qj) n αj
          (pullbackBoundaryTrivialization (cB.π.app j) (b.app j) bLim
            (cC.π.app j) (hb j) Qj τj) :=
    hframe₀.trans (congrArg (boundaryRootPowerIso bLim _ _ n αj) hτ.symm)
  refine ⟨k, e, Mk, hMk, eM, j, f, β, hrec, hframe, ?_⟩
  intro j' g
  dsimp only
  intro η _ P _ s t hst
  have hframe' := boundary_root_frame_refine
    (cB.π.app j') (B.map g) (cB.π.app j) bLim (b.app j') (b.app j)
    (cC.π.app j') (C.map g) (cC.π.app j) (cB.w g) (cC.w g)
    (hb j') (b.naturality g) (hb j) Mj Qj n β τj eLim hframe
  exact exists_boundary_root_frame_comp_eq_of_isLimit_finite B C b cB hcB cC bLim hb j'
    ((Scheme.Modules.pullback (C.map g)).obj Mj)
    ((Scheme.Modules.pullback (C.map g)).obj Qj) n
    ((Scheme.Modules.pullbackTensorPowerIso (C.map g) Mj n).symm ≪≫
      (Scheme.Modules.pullback (C.map g)).mapIso β)
    (pullbackBoundaryTrivialization (B.map g) (b.app j) (b.app j') (C.map g)
      (b.naturality g) Qj τj)
    ((Scheme.Modules.pullback bLim).mapIso
      (canIso (cC.π.app j') (C.map g) (cC.π.app j) (cC.w g) Mj) ≪≫ eLim) hframe' P s t hst

end Stacks.AlgebraicGeometry.ModuleLimits
