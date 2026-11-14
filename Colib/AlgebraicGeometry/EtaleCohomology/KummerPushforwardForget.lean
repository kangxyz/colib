/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleZModCorestriction
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerModuleComparisonNaturality

/-!
# Exact-functor forgetting of finite étale corestriction

These formulas use the actual direct image, adjunction unit and trace. They do not
identify exact-functor forgetting with the original cohomology comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe u
attribute [local instance] HasDerivedCategory.standard
namespace Stacks.EtaleCohomology
variable (n : ℕ) {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g] [IsFinite g]
attribute [local instance] finiteEtaleZModDirectImage_preservesFiniteColimits
variable [HasExt.{u + 1} (EtaleModules.{u, 0} (ZMod n) X)]
  [HasExt.{u + 1} (EtaleModules.{u, 0} (ZMod n) Y)]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

omit [Etale g] in
/-- Actual finite direct image commutes with exact-functor forgetting on Ext.
This does not assert that forgetting is bijective on Ext. -/
theorem finiteEtaleZModPushforward_forgetExt
    {A B : EtaleModules.{u, 0} (ZMod n) Y} {q : ℕ} (e : Ext.{u + 1} A B q) :
    (e.mapExactFunctor (etaleModuleDirectImage (ZMod n) g)).mapExactFunctor
        (etaleModuleForgetAb (ZMod n) X) =
    (e.mapExactFunctor (etaleModuleForgetAb (ZMod n) Y)).mapExactFunctor
        (smallEtalePushforwardAb g) := by
  rw [Stacks.ExtFunctorial.mapExactFunctor_comp_functor,
    Stacks.ExtFunctorial.mapExactFunctor_comp_functor]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting the actual corestriction is an explicit composite of the original
adjunction unit, exact direct image, and original native trace. This computes
mapExactFunctor forget; comparison with rootsOfUnityModuleExtEquiv remains separate. -/
theorem finiteEtaleZModCorestriction_forgetExt
    (A M : EtaleModules.{u, 0} (ZMod n) X) (q : ℕ)
    (e : Ext.{u + 1} ((etaleModuleInverseImage (ZMod n) g).obj A)
      ((etaleModuleInverseImage (ZMod n) g).obj M) q) :
    (finiteEtaleZModCorestriction n g A M q e).mapExactFunctor
        (etaleModuleForgetAb (ZMod n) X) =
    ((Ext.mk₀ ((smallEtaleAdjunctionAb g).unit.app
        ((etaleModuleForgetAb (ZMod n) X).obj A) ≫
      (smallEtalePushforwardAb g).map
        ((traceForgetPullbackAbIso (ZMod n) g).hom.app A))).comp
      ((e.mapExactFunctor (etaleModuleForgetAb (ZMod n) Y)).mapExactFunctor
        (smallEtalePushforwardAb g)) (zero_add q)).comp
      (Ext.mk₀ ((smallEtalePushforwardAb g).map
        ((traceForgetPullbackAbIso (ZMod n) g).inv.app M) ≫
        finiteEtaleTraceOnPullbackAb g ((etaleModuleForgetAb (ZMod n) X).obj M)))
        (add_zero q) := by
  simp only [finiteEtaleZModCorestriction, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [finiteEtaleZModPushforward_forgetExt,
    traceForgetPullbackAbIso_unit, forget_finiteEtaleZModTrace]

end Stacks.EtaleCohomology
end
