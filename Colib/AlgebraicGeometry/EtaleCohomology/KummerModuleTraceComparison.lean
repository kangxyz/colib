/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerCorestrictionSource
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerRootsOfUnityTraceCompatibility
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOriginalExtComparison
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerPushforwardForget
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerAbelianTraceBoundary

/-! # Actual module trace through the original cohomology comparison

The module corestriction, its actual constant-source map and its
actual roots-of-unity comparison are not replaced by new cohomology equivalences.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe u v w
attribute [local instance] HasDerivedCategory.standard
namespace Stacks.EtaleCohomology
open Stacks.Kummer

private theorem traceExtSandwich
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {A B C₁ D E F G : C} (a : A ⟶ B) (b : B ⟶ C₁) (c : C₁ ⟶ D)
    {q : ℕ} (e : Ext.{w} D E q) (d : E ⟶ F) (t : F ⟶ G) :
    (Ext.mk₀ a).comp
      (((Ext.mk₀ b).comp
        (((Ext.mk₀ c).comp e (zero_add q)).comp (Ext.mk₀ d) (add_zero q))
        (zero_add q)).comp (Ext.mk₀ t) (add_zero q)) (zero_add q) =
      ((Ext.mk₀ (a ≫ b ≫ c)).comp e (zero_add q)).comp
        (Ext.mk₀ (d ≫ t)) (add_zero q) := by
  simp only [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    Ext.comp_assoc_of_third_deg_zero]

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g] [IsFinite g]
  (n : ℕ) [NeZero n] (hX : IsUnit (n : Γ(X, ⊤)))
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
attribute [local instance] finiteEtaleZModDirectImage_preservesFiniteColimits

omit [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse coefficient transport cancels against the actual module trace. -/
theorem kummerModuleTraceComparison_target :
    (etaleAbelianDirectImage.{u, 0} g).map
        ((etaleModuleUnderlyingAbelian Y (ZMod n)).map
          (rootsOfUnityModuleInverseImageIso g n hX).inv) ≫
      (etaleModuleUnderlyingAbelian X (ZMod n)).map
        (finiteEtaleZModTrace n g (rootsOfUnityModule.{u, 0} X n)) =
      finiteEtaleRootsOfUnityTrace g n := by
  erw [kummerTrace_forget_rootsModule_trace g n hX]
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The original module Ext comparison sends actual finite étale corestriction of
an actual roots class on Y to its abelian constant-source push and actual Kummer trace. -/
theorem kummerModuleTraceComparison (q : ℕ)
    (e : Ext.{u + 1}
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n) Y.smallEtaleTopology)
      (rootsOfUnityModule.{u, 0} Y n) q) :
    extConstantAddEquivSheafH X (rootsOfUnityModule.{u, 0} X n) q
      (finiteEtaleZModCorestriction n g
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n) X.smallEtaleTopology)
        (rootsOfUnityModule.{u, 0} X n) q
        (((Ext.mk₀ ((etaleModuleInverseImageConstantIso (ZMod n) g).hom.app
          (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))))).comp e (zero_add q)).comp
          (Ext.mk₀ (rootsOfUnityModuleInverseImageIso g n hX).inv) (add_zero q))) =
      kummerAbelianTraceCorestriction g n q
        (extConstantAddEquivSheafH Y (rootsOfUnityModule.{u, 0} Y n) q e) := by
  let A := Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n) X.smallEtaleTopology
  let cm := (etaleModuleInverseImageConstantIso (ZMod n) g).hom.app
    (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n)))
  let r := rootsOfUnityModuleInverseImageIso g n hX
  let P := etaleAbelianDirectImage.{u, 0} g
  let UX := etaleModuleUnderlyingAbelian X (ZMod n)
  let UY := etaleModuleUnderlyingAbelian Y (ZMod n)
  let cX := etaleModuleUnderlyingAbelianConstantMap (ZMod n) X
  let cY := etaleModuleUnderlyingAbelianConstantMap (ZMod n) Y
  let unit := UX.map ((etaleModuleInverseImageAdj (ZMod n) g).unit.app A)
  let tr := UX.map (finiteEtaleZModTrace n g (rootsOfUnityModule.{u, 0} X n))
  have hs : cX ≫ unit ≫ P.map (UY.map cm) = kummerH0PushSource g ≫ P.map cY := by
    exact (kummerCorestrictionSource_unit_constant (ZMod n) g).trans
      (Category.assoc _ _ _).symm
  have ht : P.map (UY.map r.inv) ≫ tr = finiteEtaleRootsOfUnityTrace g n :=
    kummerModuleTraceComparison_target g n hX
  rw [kummerAbelianTraceCorestriction, kummerOriginalComparison_eq_extForget,
    kummerOriginalComparison_eq_extForget]
  simp only [extForgetSheafH_apply, finiteEtaleZModCorestriction,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  erw [finiteEtaleZModPushforward_forgetExt n g e]
  change (Ext.mk₀ cX).comp
      (((Ext.mk₀ unit).comp
        (((Ext.mk₀ (P.map (UY.map cm))).comp
          ((e.mapExactFunctor UY).mapExactFunctor P) (zero_add q)).comp
          (Ext.mk₀ (P.map (UY.map r.inv))) (add_zero q)) (zero_add q)).comp
        (Ext.mk₀ tr) (add_zero q)) (zero_add q) =
    ((Ext.mk₀ (kummerH0PushSource g)).comp
      ((Ext.mk₀ (P.map cY)).comp ((e.mapExactFunctor UY).mapExactFunctor P)
        (zero_add q)) (zero_add q)).comp
      (Ext.mk₀ (finiteEtaleRootsOfUnityTrace g n)) (add_zero q)
  rw [traceExtSandwich, hs, ht]
  rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]

end Stacks.EtaleCohomology
end
