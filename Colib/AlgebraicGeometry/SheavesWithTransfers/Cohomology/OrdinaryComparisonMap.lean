/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.OrdinarySource
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# The canonical map from transfer Ext to ordinary cohomology

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Transfers/Cohomology/Ext/OrdinaryComparison.lean`,
blob `eb41eab442059755edeba337ff7b7ac0511cade4`.
Only the canonical map, its Yoneda compatibility and degree-zero bijectivity
are established here. Higher-degree bijectivity requires a separate proof of
ordinary acyclicity of transfer-injectives and is not asserted in this file.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
universe w w' u
namespace AlgebraicGeometry.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
open Stacks.Cohomology.FreeYonedaUnivLE
variable (k : Type u) [Field k]
  [HasExt.{w} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{w'} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Forget transfers and pull back along the actual section source morphism. -/
def transferExtComparison (X : SmoothSite (Spec (.of k)))
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ) :
    Ext.{w} ((transferRepresentable k).obj (Cor.mk X)) F n →+
      ((cohomologyPresheaf.{w', u + 1} ((toSheaf k).obj F) n).obj (op X)) :=
  ((Ext.mk₀ (ordinaryToTransferSource k X)).precomp ((toSheaf k).obj F) (zero_add n)).comp
    ((toSheaf k).mapExtAddHom _ F n)

@[simp]
theorem transferExtComparison_mk₀ (X : SmoothSite (Spec (.of k)))
    (F : SheafWithTransfers.{u + 1} k)
    (f : (transferRepresentable k).obj (Cor.mk X) ⟶ F) :
    transferExtComparison k X F 0 (Ext.mk₀ f) =
      Ext.mk₀ (ordinaryTransferHomEquiv k X F f) := by
  change (Ext.mk₀ (ordinaryToTransferSource k X)).comp
    ((Ext.mk₀ f).mapExactFunctor (toSheaf k)) (zero_add 0) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, ← ordinaryTransferHomEquiv_apply]

/-- Comparison respects arbitrary Yoneda compositions in the coefficient variable. -/
theorem transferExtComparison_comp (X : SmoothSite (Spec (.of k)))
    {F G : SheafWithTransfers.{u + 1} k} {a b c : ℕ}
    (e : Ext.{w} ((transferRepresentable k).obj (Cor.mk X)) F a)
    (d : Ext.{w} F G b) (h : a + b = c) :
    transferExtComparison k X G c (e.comp d h) =
      (transferExtComparison k X F a e).comp (d.mapExactFunctor (toSheaf k)) h := by
  change (Ext.mk₀ (ordinaryToTransferSource k X)).comp
      ((e.comp d h).mapExactFunctor (toSheaf k)) (zero_add c) = _
  rw [Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc _ _ _ (zero_add a) h (by lia)).symm

/-- Degree zero is the actual section Hom equivalence. -/
theorem transferExtComparison_zero_bijective (X : SmoothSite (Spec (.of k)))
    (F : SheafWithTransfers.{u + 1} k) :
    Function.Bijective (transferExtComparison k X F 0) := by
  let e := (Ext.addEquiv₀ : Ext.{w} _ F 0 ≃+ (_ ⟶ F)) |>.trans
    ((ordinaryTransferHomEquiv k X F).trans Ext.addEquiv₀.symm)
  have he : ⇑(transferExtComparison k X F 0) = e := by
    funext z
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective z
    rw [transferExtComparison_mk₀]
    change Ext.mk₀ _ = Ext.mk₀ (ordinaryTransferHomEquiv k X F (Ext.addEquiv₀ (Ext.mk₀ f)))
    congr 2
    exact ((Ext.addEquiv₀ : Ext.{w} _ F 0 ≃+ (_ ⟶ F)).apply_symm_apply f).symm
  rw [he]
  exact e.bijective


end AlgebraicGeometry.SheafWithTransfers

