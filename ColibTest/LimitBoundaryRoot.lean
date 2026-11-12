/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.Invertible.LimitBoundaryRoot

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Invertible Stacks.AlgebraicGeometry.ModuleLimits

universe u

noncomputable section

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

-- Two original linear equations are enforced at a common stage after any chosen refinement.
example
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
      ∀ (P : Fin 2 → (B.obj j').Modules)
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
  obtain ⟨k, e, Mk, hMk, eM, j, f, β, hroot, hframe, hfinite⟩ :=
    exists_root_boundary_frame_of_isLimit_finite B C b cB hcB cC hcC bLim hb i L τ M n α e₀ he₀
  refine ⟨k, e, Mk, hMk, eM, j, f, β, hroot, hframe, ?_⟩
  intro j' g
  dsimp only
  intro P _ s t hst
  exact hfinite j' g P s t hst

-- With no extra equations, an actual full-boundary frame is obtained after any refinement.
example
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
      ∃ (_eM : M ≅ (Scheme.Modules.pullback (cC.π.app k)).obj Mk) (j : I) (f : j ⟶ k)
        (_β : tensorPower (C.obj j).toRingedSpace.presheaf
          (structureSheafRing (C.obj j).toRingedSpace).property
            ((Scheme.Modules.pullback (C.map f)).obj Mk) (n : ℤ) ≅
          (Scheme.Modules.pullback (C.map f)).obj
            ((Scheme.Modules.pullback (C.map e)).obj L)),
      ∀ (j' : I) (g : j' ⟶ j), ∃ (ℓ : I) (h : ℓ ⟶ j'),
        Nonempty ((Scheme.Modules.pullback (b.app ℓ)).obj
          ((Scheme.Modules.pullback (C.map h)).obj
            ((Scheme.Modules.pullback (C.map g)).obj
              ((Scheme.Modules.pullback (C.map f)).obj Mk))) ≅
          SheafOfModules.unit (B.obj ℓ).ringCatSheaf) := by
  obtain ⟨k, e, Mk, hMk, eM, j, f, β, _, _, hfinite⟩ :=
    exists_root_boundary_frame_of_isLimit_finite B C b cB hcB cC hcC bLim hb i L τ M n α e₀ he₀
  refine ⟨k, e, Mk, hMk, eM, j, f, β, ?_⟩
  intro j' g
  let P : Empty → (B.obj j').Modules := Empty.elim
  have : ∀ x, (P x).IsFinitePresentation := fun x => nomatch x
  obtain ⟨ℓ, h, eB, _⟩ := hfinite j' g P (fun x => nomatch x) (fun x => nomatch x)
    (fun x => nomatch x)
  exact ⟨ℓ, h, ⟨eB⟩⟩
