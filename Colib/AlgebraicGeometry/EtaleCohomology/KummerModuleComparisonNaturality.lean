/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerCoefficientNaturality

/-!
# Naturality of the original module-to-abelian cohomology comparison

Combine the existing integer-module comparison with coefficient-change naturality.
This concerns coefficients on one scheme, not cross-space corestriction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe u
attribute [local instance] HasDerivedCategory.standard
namespace Stacks.EtaleCohomology
variable (Y : Scheme.{u})
variable [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

-- Exact proof reused from EtaleModuleCohomologyIntComparison, without importing
-- its unrelated scalar-action comparisons.
private theorem intComparison_naturality {M M' : EtaleModules.{u, 0} ℤ Y} (g : M ⟶ M')
    (i : ℕ) (y : (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} ℤ
        Y.smallEtaleTopology) i).obj M) :
    extConstantIntAddEquivSheafH Y M' i
        ((extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} ℤ
          Y.smallEtaleTopology) i).map g y) =
      Sheaf.H.map ((etaleModuleUnderlyingAbelian Y ℤ).map g) i
        (extConstantIntAddEquivSheafH Y M i y) := by
  have : (etaleModuleUnderlyingAbelian Y ℤ).Additive :=
    ⟨fun {_ _ _ _} => by
      ext U : 3
      exact (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).map_add⟩
  have key : ∀ z : Abelian.Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} ℤ
      Y.smallEtaleTopology) M i,
      (Abelian.Ext.mk₀ (etaleModuleUnderlyingAbelianConstantIso.{u} Y).symm.hom).comp
          ((z.comp (Abelian.Ext.mk₀ g) (add_zero i)).mapExactFunctor
            (etaleModuleUnderlyingAbelian Y ℤ)) (zero_add i) =
        ((Abelian.Ext.mk₀ (etaleModuleUnderlyingAbelianConstantIso.{u} Y).symm.hom).comp
          (z.mapExactFunctor (etaleModuleUnderlyingAbelian Y ℤ)) (zero_add i)).comp
          (Abelian.Ext.mk₀ ((etaleModuleUnderlyingAbelian Y ℤ).map g)) (add_zero i) := by
    intro z
    rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
      Abelian.Ext.comp_assoc_of_third_deg_zero]
  exact key y


set_option maxRecDepth 4096 in
/-- Coefficient naturality of the exact existing equivalence used by KummerModuleClass. -/
theorem kummerExtConstantAddEquivSheafH_naturality
    {Λ : Type} [CommRing Λ] {M M' : EtaleModules.{u, 0} Λ Y} (φ : M ⟶ M')
    (i : ℕ) (x : (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        Y.smallEtaleTopology) i).obj M) :
    extConstantAddEquivSheafH Y M' i
      ((extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        Y.smallEtaleTopology) i).map φ x) =
    Sheaf.H.map ((etaleModuleUnderlyingAbelian Y Λ).map φ) i
      (extConstantAddEquivSheafH Y M i x) := by
  have hR := ConcreteCategory.congr_hom
    (kummerExtConstantRestrictScalarsIso_hom_naturality Y φ i) x
  have hA := intComparison_naturality Y
    ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).map φ) i
    ((extConstantRestrictScalarsIso (Int.castRingHom Λ) Y M i).hom x)
  exact (congrArg (extConstantIntAddEquivSheafH Y _ i) hR).trans hA

end Stacks.EtaleCohomology
end
