/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOriginalExtZero
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOriginalCoefficientSucc

/-! # Equality of the original and exact-forgetful Kummer comparisons

The coefficient calculation uses the actual chosen-resolution maps in degree zero and
in positive degrees. The integral-to-abelian tail is the previously proved original tail.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
universe u
attribute [local instance] HasDerivedCategory.standard
namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- In every degree the original coefficient map is exact restriction followed by
precomposition with the actual corepresenting constant-source map. -/
theorem kummerOriginalCoefficient_eq
    (M : EtaleModules.{u, 0} Λ X) (q : ℕ)
    (x : Ext.{u + 1}
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) M q) :
    (extConstantRestrictScalarsIso (Int.castRingHom Λ) X M q).hom x =
      (Ext.mk₀ (kummerConstantRestrictionHom Λ X)).comp
        (x.mapExactFunctor (etaleModuleRestrictScalars (Int.castRingHom Λ) X)) (zero_add q) := by
  cases q with
  | zero => exact kummerOriginalCoefficient_zero Λ X M x
  | succ n => exact kummerOriginalCoefficient_succ Λ X M n x

variable [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The original derived Ext-to-sheaf-cohomology comparison equals the named map
constructed by exact forgetting and its named constant-source morphism. -/
theorem kummerOriginalComparison_eq_extForget
    (M : EtaleModules.{u, 0} Λ X) (q : ℕ)
    (x : Ext.{u + 1}
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) M q) :
    extConstantAddEquivSheafH X M q x = extForgetSheafH Λ X M q x := by
  exact (kummerOriginalComparison_eq_iff_coefficient Λ X M q x).mpr
    (kummerOriginalCoefficient_eq Λ X M q x)

end Stacks.EtaleCohomology
end
