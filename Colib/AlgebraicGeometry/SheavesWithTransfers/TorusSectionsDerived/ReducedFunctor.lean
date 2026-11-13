/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.DerivedCategory.SplitEpiKernel
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.UnitSplit
public import Colib.CategoryTheory.Preadditive.SplitCokernelKernel

/-!
# Reduced total derived torus sections

The reduced functor is the kernel of the actual total derived restriction
to the unit. The original constant sections give its split projection.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k] [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

instance (K : DerivedCategory (SheafWithTransfers.{u + 1} k)) :
    HasKernel ((torusSectionsDerivedUnitRestriction k).app K) :=
  Pretriangulated.hasKernel_of_section _ ((torusSectionsDerivedConstant k).app K)
    (NatTrans.congr_app (torusSectionsDerivedConstant_comp_unit k) K)

/-- The induced map on the kernels of the actual unit restriction. -/
def reducedTorusSectionsDerivedMap {K L : DerivedCategory (SheafWithTransfers.{u + 1} k)}
    (f : K ⟶ L) :
    kernel ((torusSectionsDerivedUnitRestriction k).app K) ⟶
      kernel ((torusSectionsDerivedUnitRestriction k).app L) :=
  kernel.lift ((torusSectionsDerivedUnitRestriction k).app L)
    (kernel.ι ((torusSectionsDerivedUnitRestriction k).app K) ≫
      (torusSectionsDerivedFunctor k).map f) (by
    rw [Category.assoc, (torusSectionsDerivedUnitRestriction k).naturality f,
      ← Category.assoc, kernel.condition, zero_comp])

@[reassoc]
theorem reducedTorusSectionsDerivedMap_ι
    {K L : DerivedCategory (SheafWithTransfers.{u + 1} k)} (f : K ⟶ L) :
    reducedTorusSectionsDerivedMap k f ≫
        kernel.ι ((torusSectionsDerivedUnitRestriction k).app L) =
      kernel.ι ((torusSectionsDerivedUnitRestriction k).app K) ≫
        (torusSectionsDerivedFunctor k).map f :=
  kernel.lift_ι _ _ _

/-- The kernel of the literal unit restriction, with its induced original
coefficient maps. -/
def reducedTorusSectionsDerivedFunctor :
    DerivedCategory (SheafWithTransfers.{u + 1} k) ⥤
      DerivedCategory (SheafWithTransfers.{u + 1} k) where
  obj K := kernel ((torusSectionsDerivedUnitRestriction k).app K)
  map f := reducedTorusSectionsDerivedMap k f
  map_id K := by
    apply (cancel_mono (kernel.ι ((torusSectionsDerivedUnitRestriction k).app K))).mp
    rw [reducedTorusSectionsDerivedMap_ι, CategoryTheory.Functor.map_id, Category.comp_id,
      Category.id_comp]
  map_comp {_ _ M} f g := by
    apply (cancel_mono (kernel.ι ((torusSectionsDerivedUnitRestriction k).app M))).mp
    simp only [Category.assoc, reducedTorusSectionsDerivedMap_ι,
      reducedTorusSectionsDerivedMap_ι_assoc, CategoryTheory.Functor.map_comp]

/-- Include the actual reduced summand into total derived torus sections. -/
def reducedTorusSectionsDerivedInclusion :
    reducedTorusSectionsDerivedFunctor k ⟶ torusSectionsDerivedFunctor k := by
  unfold reducedTorusSectionsDerivedFunctor
  exact
    { app := fun K => kernel.ι ((torusSectionsDerivedUnitRestriction k).app K)
      naturality := fun {_ _} f => reducedTorusSectionsDerivedMap_ι k f }

/-- The projection removes the original unit-constant component. -/
def reducedTorusSectionsDerivedProjection :
    torusSectionsDerivedFunctor k ⟶ reducedTorusSectionsDerivedFunctor k := by
  let R := torusSectionsDerivedFunctor k
  let u := torusSectionsDerivedUnitRestriction k
  let c := torusSectionsDerivedConstant k
  let r (K : DerivedCategory (SheafWithTransfers.{u + 1} k)) :=
    splitKernelProjection (c.app K) (u.app K)
      (NatTrans.congr_app (torusSectionsDerivedConstant_comp_unit k) K)
  unfold reducedTorusSectionsDerivedFunctor
  refine { app := r, naturality := ?_ }
  intro K L f
  change R.map f ≫ r L = r K ≫ reducedTorusSectionsDerivedMap k f
  let ι (M : DerivedCategory (SheafWithTransfers.{u + 1} k)) := kernel.ι (u.app M)
  have hr (M : DerivedCategory (SheafWithTransfers.{u + 1} k)) :
      r M ≫ ι M = 𝟙 _ - u.app M ≫ c.app M :=
    splitKernelProjection_ι _ _ (NatTrans.congr_app (torusSectionsDerivedConstant_comp_unit k) M)
  have h : R.map f ≫ u.app L ≫ c.app L = u.app K ≫ c.app K ≫ R.map f :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ c.app L) (u.naturality f)).trans
        ((Category.assoc _ _ _).trans (congrArg (u.app K ≫ ·) (c.naturality f))))
  apply (cancel_mono (ι L)).mp
  calc
    _ = R.map f ≫ (r L ≫ ι L) := Category.assoc _ _ _
    _ = R.map f ≫ (𝟙 _ - u.app L ≫ c.app L) := congrArg (R.map f ≫ ·) (hr L)
    _ = (𝟙 _ - u.app K ≫ c.app K) ≫ R.map f := by
      rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp,
        Category.assoc, h]
    _ = (r K ≫ ι K) ≫ R.map f := congrArg (· ≫ R.map f) (hr K).symm
    _ = r K ≫ (ι K ≫ R.map f) := Category.assoc _ _ _
    _ = r K ≫ (reducedTorusSectionsDerivedMap k f ≫ ι L) :=
      congrArg (r K ≫ ·) (reducedTorusSectionsDerivedMap_ι k f).symm
    _ = _ := (Category.assoc _ _ _).symm

/-- The actual inclusion and projection split. -/
@[reassoc]
theorem reducedTorusSectionsDerivedInclusion_projection (K :
    DerivedCategory (SheafWithTransfers.{u + 1} k)) :
    (reducedTorusSectionsDerivedInclusion k).app K ≫
      (reducedTorusSectionsDerivedProjection k).app K = 𝟙 _ := by
  unfold reducedTorusSectionsDerivedInclusion reducedTorusSectionsDerivedProjection
  let u := (torusSectionsDerivedUnitRestriction k).app K
  let c := (torusSectionsDerivedConstant k).app K
  have h : c ≫ u = 𝟙 K := NatTrans.congr_app (torusSectionsDerivedConstant_comp_unit k) K
  change kernel.ι u ≫ splitKernelProjection c u h = 𝟙 _
  apply (cancel_mono (kernel.ι u)).mp
  rw [Category.assoc, splitKernelProjection_ι, Preadditive.comp_sub, Category.comp_id,
    ← Category.assoc, kernel.condition, zero_comp, sub_zero, Category.id_comp]

/-- The reverse composite is exactly the complement of the original
constant summand. -/
@[reassoc]
theorem reducedTorusSectionsDerivedProjection_inclusion (K :
    DerivedCategory (SheafWithTransfers.{u + 1} k)) :
    (reducedTorusSectionsDerivedProjection k).app K ≫
      (reducedTorusSectionsDerivedInclusion k).app K =
    𝟙 _ - (torusSectionsDerivedUnitRestriction k).app K ≫
      (torusSectionsDerivedConstant k).app K := by
  unfold reducedTorusSectionsDerivedInclusion reducedTorusSectionsDerivedProjection
  exact splitKernelProjection_ι _ _
    (NatTrans.congr_app (torusSectionsDerivedConstant_comp_unit k) K)

end AlgebraicGeometry.SheafWithTransfers
