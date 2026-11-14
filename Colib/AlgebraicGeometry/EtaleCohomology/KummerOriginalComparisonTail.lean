/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerNamedConstantMap

/-!
# Original integer-to-abelian tail of the Kummer comparison

Identify the actual integer-to-abelian tail, using the proved
original named source map. The second result is an explicit reduction, NOT a proof
of equality of the original comparisons; no unproved comparison equality is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe u
namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})
variable [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

set_option maxRecDepth 4096 in
/-- The original integral-to-abelian equivalence sends exact coefficient restriction
with the actual corepresenting source map to the existing named forgetful Ext map. -/
theorem kummerOriginalIntTail_eq_extForget (M : EtaleModules.{u, 0} Λ X) (q : ℕ)
    (e : Ext.{u + 1}
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) M q) :
    extConstantIntAddEquivSheafH X
      ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M) q
      ((Ext.mk₀ (kummerConstantRestrictionHom Λ X)).comp
        (e.mapExactFunctor (etaleModuleRestrictScalars (Int.castRingHom Λ) X))
        (zero_add q)) = extForgetSheafH Λ X M q e := by
  change (Ext.mk₀ (etaleModuleUnderlyingAbelianConstantIso X).inv).comp
      (((Ext.mk₀ (kummerConstantRestrictionHom Λ X)).comp
        (e.mapExactFunctor (etaleModuleRestrictScalars (Int.castRingHom Λ) X))
        (zero_add q)).mapExactFunctor (etaleModuleUnderlyingAbelian X ℤ))
      (zero_add q) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    kummerConstantRestriction_eq_originalConstantMap,
    Stacks.ExtFunctorial.mapExactFunctor_comp_functor]
  rfl

set_option maxRecDepth 4096 in
/-- Exact reduction of the remaining ORIGINAL comparison equality to the integral
coefficient step. This does not assert that either side of the equivalence holds. -/
theorem kummerOriginalComparison_eq_iff_coefficient (M : EtaleModules.{u, 0} Λ X) (q : ℕ)
    (e : Ext.{u + 1}
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) M q) :
    extConstantAddEquivSheafH X M q e = extForgetSheafH Λ X M q e ↔
      (extConstantRestrictScalarsIso (Int.castRingHom Λ) X M q).hom e =
        (Ext.mk₀ (kummerConstantRestrictionHom Λ X)).comp
          (e.mapExactFunctor (etaleModuleRestrictScalars (Int.castRingHom Λ) X))
          (zero_add q) := by
  rw [← kummerOriginalIntTail_eq_extForget Λ X M q e]
  exact (extConstantIntAddEquivSheafH X
    ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M) q).injective.eq_iff

end Stacks.EtaleCohomology
end
