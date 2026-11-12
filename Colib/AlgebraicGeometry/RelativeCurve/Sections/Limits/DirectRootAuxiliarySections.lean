/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.AuxiliaryFinitePair
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.DirectRootTensorSectionRefinement

/-! # Original auxiliary sections descend with the direct fixed root model

The auxiliary invertible module and both actual sections are chosen internally.
The root is the direct pullback from the already specified root stage; the native
tensor and canonical comparisons recover both original section values.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.SheafOfModules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Modules

local instance instDirectRootAuxiliarySectionsStacksInvertible
    {X : Scheme.{u}} (M : X.Modules)
    [hM : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hM

local instance instDirectRootAuxiliarySectionsInvertiblePullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [hM : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property ((pullback f).obj M) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom M hM

local instance instDirectRootAuxiliarySectionsInvertiblePair
    {X : Scheme.{u}} (M N : X.Modules)
    [hM : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    [hN : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] (z : Bool) :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (auxiliaryPairModules M N z) := by
  cases z
  · exact hN
  · exact (Stacks.SheafOfModules.isInvertible_tensorSheaf
      X.sheaf.obj X.ringCatSheaf.property M N).toAlgebraicGeometry

/-- Choose the original auxiliary module and both sections after the fixed root
stage. Their actual final tensor uses the direct composite root pullback. -/
theorem exists_directRoot_auxiliarySections_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (C : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (C.map f)]
    (c : Cone C) (hc : IsLimit c) [∀ i, CompactSpace (C.obj i)]
    [∀ i, QuasiSeparatedSpace (C.obj i)] (i : I) (L : (C.obj i).Modules)
    [SheafOfModules.IsInvertible (C.obj i).sheaf.obj (C.obj i).ringCatSheaf.property L]
    (M N : c.pt.Modules) (E : M ≅ (pullback (c.π.app i)).obj L)
    (hN : SheafOfModules.IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property N)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor c.pt.sheaf).obj M).obj N, ⊤))
    (b : Γ(N, ⊤)) :
    ∃ (j : I) (e : j ⟶ i) (Nj : (C.obj j).Modules)
      (_hNj : SheafOfModules.IsInvertible (C.obj j).sheaf.obj (C.obj j).ringCatSheaf.property Nj)
      (F : N ≅ (pullback (c.π.app j)).obj Nj) (k : I) (f : k ⟶ j)
      (a' : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor (C.obj k).sheaf).obj
        ((pullback (C.map (f ≫ e))).obj L)).obj ((pullback (C.map f)).obj Nj), ⊤))
      (b' : Γ((pullback (C.map f)).obj Nj, ⊤)),
      Hom.app
        (tensorProductIso c.pt.sheaf.obj c.pt.ringCatSheaf.property
          (refinedSectionModelIso (c.π.app k) (C.map (f ≫ e)) (c.π.app i) (c.w (f ≫ e)) L E)
          (refinedSectionModelIso (c.π.app k) (C.map f) (c.π.app j) (c.w f) Nj F) ≪≫
          (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (c.π.app k)
            ((pullback (C.map (f ≫ e))).obj L) ((pullback (C.map f)).obj Nj)).symm).hom ⊤ a =
        pullbackGlobalSections (c.π.app k) _ a' ∧
      Hom.app (refinedSectionModelIso (c.π.app k) (C.map f) (c.π.app j) (c.w f) Nj F).hom ⊤ b =
        pullbackGlobalSections (c.π.app k) _ b' := by
  obtain ⟨j, e, Nj, hNj, F, _⟩ :=
    exists_auxiliaryInvertible_tensorModel_of_isLimit C c hc i L M N E hN
  let := hNj
  let V := auxiliaryPairModules ((pullback (C.map e)).obj L) Nj
  let EM := auxiliaryPairModelIsos (c.π.app j) (C.map e) (c.π.app i) (c.w e) L Nj M N E F
  let (z : Bool) : (V z).IsFinitePresentation :=
    @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible (C.obj j) (V z)
      (inferInstanceAs (SheafOfModules.IsInvertible
        (C.obj j).sheaf.obj (C.obj j).ringCatSheaf.property (V z)))
  obtain ⟨k, f, t, ht⟩ := exists_globalSections_pullback_canonical_of_isLimit_finite C c hc j V
    (fun z => Hom.app (EM z).hom ⊤ (auxiliaryPairSections M N a b z))
  let a' := Hom.app
    (tensorProductIso (C.obj k).sheaf.obj (C.obj k).ringCatSheaf.property
      (canIso (C.map f) (C.map e) (C.map (f ≫ e)) (C.map_comp f e).symm L)
      (Iso.refl ((pullback (C.map f)).obj Nj))).hom ⊤
    (Hom.app (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (C.map f)
      ((pullback (C.map e)).obj L) Nj).hom ⊤ (t true))
  refine ⟨j, e, Nj, hNj, F, k, f, a', t false, ?_, ?_⟩
  · apply directRootTensorSection_refinement (c.π.app k) (C.map f) (C.map e)
      (c.π.app j) (C.map (f ≫ e)) (c.π.app i) (c.w f) (C.map_comp f e).symm
      (c.w e) (c.w (f ≫ e)) L Nj M N E F a (t true)
    exact refinedSectionModelIso_recovery (c.π.app k) (C.map f) (c.π.app j) (c.w f)
      (V true) (EM true) a (t true) (ht true)
  · exact refinedSectionModelIso_recovery (c.π.app k) (C.map f) (c.π.app j) (c.w f)
      Nj F b (t false) (ht false)

end AlgebraicGeometry.Scheme.Modules
