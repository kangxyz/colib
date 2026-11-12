/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.DirectRootAuxiliarySections
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.BoundarySectionFrames
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.BoundaryFrameRecovery

/-! # Original auxiliary frame and pair at the same direct-root refinement

The original auxiliary module, sections and boundary frame are all descended
internally after the fixed root model. One final direct root refinement retains
both original section values and the actual original auxiliary boundary frame.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.SheafOfModules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Modules

local instance instDirectRootAuxiliaryFramesStacksInvertible
    {X : Scheme.{u}} (M : X.Modules)
    [hM : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hM

local instance instDirectRootAuxiliaryFramesInvertiblePullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [hM : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property ((pullback f).obj M) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom M hM

local instance instDirectRootAuxiliaryFramesInvertiblePair
    {X : Scheme.{u}} (M N : X.Modules)
    [hM : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    [hN : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] (z : Bool) :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (auxiliaryPairModules M N z) := by
  cases z
  · exact hN
  · exact (Stacks.SheafOfModules.isInvertible_tensorSheaf
      X.sheaf.obj X.ringCatSheaf.property M N).toAlgebraicGeometry

/-- Descend the original auxiliary pair and boundary frame together after a
specified root stage, retaining its direct root model and original numerator. -/
theorem exists_directRoot_auxiliaryFrames_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (B C : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (C.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
    (c : Cone C) (hc : IsLimit c) [∀ i, CompactSpace (C.obj i)]
    [∀ i, QuasiSeparatedSpace (C.obj i)]
    (ι : B ⟶ C) (cB : Cone B) (hcB : IsLimit cB)
    [∀ i, CompactSpace (B.obj i)] [∀ i, QuasiSeparatedSpace (B.obj i)]
    (bLim : cB.pt ⟶ c.pt) (hSquare : ∀ i, cB.π.app i ≫ ι.app i = bLim ≫ c.π.app i)
    (i : I) (L : (C.obj i).Modules)
    [SheafOfModules.IsInvertible (C.obj i).sheaf.obj (C.obj i).ringCatSheaf.property L]
    (M N : c.pt.Modules) (E : M ≅ (pullback (c.π.app i)).obj L)
    (hN : SheafOfModules.IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property N)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor c.pt.sheaf).obj M).obj N, ⊤))
    (b : Γ(N, ⊤)) (eN : (pullback bLim).obj N ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    (hb : Hom.app eN.hom ⊤ (pullbackGlobalSections bLim N b) = (1 : Γ(cB.pt, ⊤))) :
    ∃ (j : I) (d : j ⟶ i) (Nj : (C.obj j).Modules)
      (_hNj : SheafOfModules.IsInvertible (C.obj j).sheaf.obj (C.obj j).ringCatSheaf.property Nj)
      (F : N ≅ (pullback (c.π.app j)).obj Nj)
      (eAux : (pullback (ι.app j)).obj Nj ≅ SheafOfModules.unit (B.obj j).ringCatSheaf)
      (a' : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor (C.obj j).sheaf).obj
        ((pullback (C.map d)).obj L)).obj Nj, ⊤)) (b' : Γ(Nj, ⊤)),
      Hom.app
        (tensorProductIso c.pt.sheaf.obj c.pt.ringCatSheaf.property
          (refinedSectionModelIso (c.π.app j) (C.map d) (c.π.app i) (c.w d) L E) F ≪≫
          (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (c.π.app j)
            ((pullback (C.map d)).obj L) Nj).symm).hom ⊤ a =
        pullbackGlobalSections (c.π.app j) _ a' ∧
      Hom.app F.hom ⊤ b = pullbackGlobalSections (c.π.app j) Nj b' ∧
      pullbackBoundaryTrivialization (cB.π.app j) (ι.app j) bLim (c.π.app j)
        (hSquare j) Nj eAux = ((pullback bLim).mapIso F).symm ≪≫ eN ∧
      Hom.app eAux.hom ⊤ (pullbackGlobalSections (ι.app j) Nj b') = (1 : Γ(B.obj j, ⊤)) := by
  obtain ⟨j, e, Nj, hNj, F, k, f, a', b', ha, hb'⟩ :=
    exists_directRoot_auxiliarySections_of_isLimit C c hc i L M N E hN a b
  let := hNj
  let Nk := (pullback (C.map f)).obj Nj
  let Fk := refinedSectionModelIso (c.π.app k) (C.map f) (c.π.app j) (c.w f) Nj F
  let _ : Nk.IsFinitePresentation :=
    @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible (C.obj k) Nk
      (inferInstanceAs (SheafOfModules.IsInvertible
        (C.obj k).sheaf.obj (C.obj k).ringCatSheaf.property Nk))
  obtain ⟨l, g, eAux, he, hOne⟩ :=
    exists_original_boundaryFrame_modeledSections_one_of_isLimit B C ι cB hcB c bLim hSquare
      k Nk N Fk eN (fun _ : PUnit.{1} => b) (fun _ => b') (fun _ => hb') (fun _ => hb)
  let Nl := (pullback (C.map g)).obj Nk
  let Fl := refinedSectionModelIso (c.π.app l) (C.map g) (c.π.app k) (c.w g) Nk Fk
  let al := Hom.app
    (tensorProductIso (C.obj l).sheaf.obj (C.obj l).ringCatSheaf.property
      (canIso (C.map g) (C.map (f ≫ e)) (C.map (g ≫ (f ≫ e)))
        (C.map_comp g (f ≫ e)).symm L) (Iso.refl Nl)).hom ⊤
    (Hom.app (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (C.map g)
      ((pullback (C.map (f ≫ e))).obj L) Nk).hom ⊤
      (pullbackGlobalSections (C.map g) _ a'))
  refine ⟨l, g ≫ (f ≫ e), Nl, inferInstance, Fl, eAux, al,
    pullbackGlobalSections (C.map g) Nk b', ?_, ?_, ?_, hOne PUnit.unit⟩
  · apply directRootTensorSection_refinement (c.π.app l) (C.map g) (C.map (f ≫ e))
      (c.π.app k) (C.map (g ≫ (f ≫ e))) (c.π.app i) (c.w g)
      (C.map_comp g (f ≫ e)).symm (c.w (f ≫ e)) (c.w (g ≫ (f ≫ e))) L Nk M N E Fk a
      (pullbackGlobalSections (C.map g) _ a')
    exact refinedSectionModelIso_pullback_recovery (c.π.app l) (C.map g)
      (c.π.app k) (c.w g) _ _ a a' ha
  · exact refinedSectionModelIso_pullback_recovery (c.π.app l) (C.map g)
      (c.π.app k) (c.w g) Nk Fk b b' hb'
  · exact boundaryFrame_originalModel_recovery B C ι cB c bLim hSquare g Nk N Fk eN eAux he

end AlgebraicGeometry.Scheme.Modules
