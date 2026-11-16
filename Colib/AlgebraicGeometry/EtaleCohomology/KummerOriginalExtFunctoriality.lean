/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOriginalExtComparison

/-! # Restriction and boundary compatibility of the original Kummer comparison

The original derived comparison, not a replacement equivalence, commutes with
cross-scheme restriction and exact-sequence boundaries. These are consequences of
its proved equality with exact forgetting. Norm compatibility is a separate step.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe u
attribute [local instance] HasDerivedCategory.standard
namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] {X Y : Scheme.{u}}
variable [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- Cross-scheme restriction under the actual original derived comparison. -/
theorem kummerOriginalComparison_restriction (g : Y ⟶ X)
    (M : EtaleModules.{u, 0} Λ X) {q : ℕ}
    (a : Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
      X.smallEtaleTopology) M q) :
    extConstantAddEquivSheafH Y _ q (etaleModuleExtRestriction Λ g M q a) =
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} g
        ((etaleModuleUnderlyingAbelian X Λ).obj M) q
        (extConstantAddEquivSheafH X M q a)).comp
        (Ext.mk₀ ((etaleModuleUnderlyingAbelianInverseImageIso Λ g).hom.app M))
        (add_zero q) := by
  simp only [kummerOriginalComparison_eq_extForget]
  exact extForgetSheafH_etaleModuleExtRestriction Λ g M a

/-- Exact-sequence connecting maps under the actual original derived comparison. -/
theorem kummerOriginalComparison_boundary
    {S : ShortComplex (EtaleModules.{u, 0} Λ X)} (hS : S.ShortExact) {q : ℕ}
    (a : Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
      X.smallEtaleTopology) S.X₃ q) :
    extConstantAddEquivSheafH X S.X₁ (q + 1) (a.comp hS.extClass rfl) =
      (extConstantAddEquivSheafH X S.X₃ q a).comp
        (hS.map_of_exact (etaleModuleUnderlyingAbelian X Λ)).extClass rfl := by
  simp only [kummerOriginalComparison_eq_extForget]
  exact extForgetSheafH_comp_extClass Λ X hS a

end Stacks.EtaleCohomology
end
