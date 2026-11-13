/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ContractionFunctor
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedComparison.SingularEvaluation
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedComparison.SingularUnit

/-!
# The reduced summand of the original singular comparison

The original contraction-kernel inclusion is split before taking
singular cochains. The derived comparison carries it to the kernel of
the actual unit restriction on total derived torus sections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe w w' w'' u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

local notation "C" => singularSheafCochainFunctor k 0 ⋙ DerivedCategory.Q

private instance : (singularSheafCochainFunctor k 0).Additive := by
  unfold singularSheafCochainFunctor singularCochainFunctor
  infer_instance

/-- The original contraction-kernel map into actual total derived torus sections. -/
def singularDerivedTorusKernelInclusion (P : PresheafWithTransfers.{u + 1} k) :
    (C).obj (contractionKernel P) ⟶
      (torusSectionsDerivedFunctor k).obj ((C).obj P) :=
  (C).map (kernel.ι (torusUnit P)) ≫ singularSheafDerivedTorusSectionsMap k P

/-- The original contraction-kernel map is annihilated by actual unit restriction. -/
@[reassoc]
theorem singularDerivedTorusKernelInclusion_unit (P : PresheafWithTransfers.{u + 1} k) :
    singularDerivedTorusKernelInclusion k P ≫
      (torusSectionsDerivedUnitRestriction k).app ((C).obj P) = 0 := by
  let E := C
  let i := kernel.ι (torusUnit P)
  let u := torusUnit P
  let e := baseSectionsPresheafIso k P
  let f := singularSheafDerivedTorusSectionsMap k P
  let r := (torusSectionsDerivedUnitRestriction k).app (E.obj P)
  change (E.map i ≫ f) ≫ r = 0
  calc
    _ = E.map i ≫ (f ≫ r) := Category.assoc _ _ _
    _ = E.map i ≫ E.map (u ≫ e.inv) :=
      congrArg (E.map i ≫ ·) (singularSheafDerivedTorusSectionsMap_comp_unit k P)
    _ = E.map (i ≫ (u ≫ e.inv)) := (E.map_comp _ _).symm
    _ = _ := by rw [← Category.assoc, kernel.condition, zero_comp,
      CategoryTheory.Functor.map_zero]

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [PerfectField k]

/-- The literal contraction-kernel inclusion exhibits the kernel of the
actual total-derived restriction to the unit. -/
def singularDerivedTorusKernelIsLimit (P : PresheafWithTransfers.{u + 1} k) :
    IsLimit (KernelFork.ofι (singularDerivedTorusKernelInclusion k P)
      (singularDerivedTorusKernelInclusion_unit k P)) := by
  let E := C
  let f := singularSheafDerivedTorusSectionsMap k P
  let u₀ := torusUnit P
  let c := torusConstant P
  let i := kernel.ι u₀
  let r := contractionKernelProjection P
  let e := baseSectionsPresheafIso k P
  let U := (torusSectionsDerivedUnitRestriction k).app (E.obj P)
  let j := singularDerivedTorusKernelInclusion k P
  let : IsIso f := isIso_singularSheafDerivedTorusSectionsMap k P
  have hir : i ≫ r = 𝟙 _ :=
    NatTrans.congr_app (contractionKernelInclusion_retraction (k := k)) P
  let : IsSplitMono (E.map i) :=
    IsSplitMono.mk' ⟨E.map r, (E.map_comp i r).symm.trans
      ((congrArg E.map hir).trans (E.map_id _))⟩
  let : Mono (E.map i) := inferInstance
  let : Mono j := inferInstanceAs (Mono (E.map i ≫ f))
  refine KernelFork.IsLimit.ofι' j (singularDerivedTorusKernelInclusion_unit k P) ?_
  intro W g hg
  let g₀ : W ⟶ E.obj (torusSections P) := g ≫ inv f
  have hf : f ≫ U = E.map (u₀ ≫ e.inv) := singularSheafDerivedTorusSectionsMap_comp_unit k P
  have hg₀ : g₀ ≫ E.map u₀ = 0 := by
    apply (cancel_mono (E.mapIso e.symm).hom).1
    calc
      _ = g₀ ≫ E.map (u₀ ≫ e.inv) := by
        change (g₀ ≫ E.map u₀) ≫ E.map e.inv = _
        exact (Category.assoc _ _ _).trans (congrArg (g₀ ≫ ·) (E.map_comp _ _).symm)
      _ = g ≫ U := by simp only [← hf, g₀, Category.assoc, IsIso.inv_hom_id_assoc]
      _ = _ := hg.trans
        (show (0 : W ⟶ E.obj (baseSections P)) ≫ (E.mapIso e.symm).hom = 0 from
          zero_comp).symm
  refine ⟨g₀ ≫ E.map r, ?_⟩
  change (g₀ ≫ E.map r) ≫ E.map i ≫ f = g
  calc
    _ = g₀ ≫ E.map (r ≫ i) ≫ f := by simp only [Category.assoc, E.map_comp]
    _ = g₀ ≫ (𝟙 _ - E.map u₀ ≫ E.map c) ≫ f := by
      rw [contractionKernelProjection_ι, CategoryTheory.Functor.map_sub, E.map_id, E.map_comp]
    _ = (g₀ ≫ (𝟙 _ - E.map u₀ ≫ E.map c)) ≫ f := (Category.assoc _ _ _).symm
    _ = g₀ ≫ f := by
      have hh : g₀ ≫ (𝟙 _ - E.map u₀ ≫ E.map c) = g₀ := by
        calc
          _ = g₀ - (g₀ ≫ E.map u₀) ≫ E.map c := by
            rw [Preadditive.comp_sub, Category.comp_id]
            exact congrArg (g₀ - ·) (Category.assoc g₀ (E.map u₀) (E.map c)).symm
          _ = g₀ := by rw [hg₀, zero_comp, sub_zero]
      exact congrArg (· ≫ f) hh
    _ = _ := (Category.assoc _ _ _).trans
      ((congrArg (g ≫ ·) (IsIso.inv_hom_id f)).trans (Category.comp_id _))

end AlgebraicGeometry.SheafWithTransfers
