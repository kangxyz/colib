/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerNamedConstantMap

/-!
# Integral comparison on the actual chosen resolution cocycles

Use exactly the chosen comparison already used in derived-unit transport.
Neither the restricted resolution nor the forgetful functor is assumed injective.
The original derived Ext comparison equality is not asserted by these lemmas.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe u
namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- The actual restricted cocycle with the original corepresenting source is closed. -/
theorem kummerIntegralResolution_cocycle (M : EtaleModules.{u, 0} Λ X) (q : ℕ)
    (t : Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology ⟶
      (injectiveResolution M).cocomplex.X q)
    (ht : t ≫ (injectiveResolution M).cocomplex.d q (q + 1) = 0) :
    (kummerConstantRestrictionHom Λ X ≫
      (etaleModuleRestrictScalars (Int.castRingHom Λ) X).map t ≫
      (kummerRestrictedResolutionComparison Λ X M).f q) ≫
      (injectiveResolution ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M)).cocomplex.d
        q (q + 1) = 0 := by
  rw [Category.assoc]
  exact (congrArg (kummerConstantRestrictionHom Λ X ≫ ·)
    (Stacks.Cohomology.ModuleComparison.extMk_map_comp_eq_zero
      (etaleModuleRestrictScalars (Int.castRingHom Λ) X)
      (injectiveResolution M)
      (injectiveResolution ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M))
      (kummerRestrictedResolutionComparison Λ X M) t rfl ht)).trans Limits.comp_zero

/-- The exact integral coefficient map on a class uses the same chosen resolution map
as the verified original derived-unit formula. -/
theorem kummerIntegralResolution_extMk (M : EtaleModules.{u, 0} Λ X) (q : ℕ)
    (t : Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology ⟶
      (injectiveResolution M).cocomplex.X q)
    (ht : t ≫ (injectiveResolution M).cocomplex.d q (q + 1) = 0) :
    (Ext.mk₀ (kummerConstantRestrictionHom Λ X)).comp
      (((injectiveResolution M).extMk t (q + 1) rfl ht).mapExactFunctor
        (etaleModuleRestrictScalars (Int.castRingHom Λ) X)) (zero_add q) =
      (injectiveResolution ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M)).extMk
        (kummerConstantRestrictionHom Λ X ≫
          (etaleModuleRestrictScalars (Int.castRingHom Λ) X).map t ≫
          (kummerRestrictedResolutionComparison Λ X M).f q) (q + 1) rfl
        (kummerIntegralResolution_cocycle Λ X M q t ht) := by
  rw [Stacks.Cohomology.ModuleComparison.mapExactFunctor_extMk
      (etaleModuleRestrictScalars (Int.castRingHom Λ) X)
      (injectiveResolution M)
      (injectiveResolution ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M))
      (kummerRestrictedResolutionComparison Λ X M)
      (kummerRestrictedResolutionComparison_augmentation Λ X M),
    InjectiveResolution.mk₀_comp_extMk]

set_option backward.isDefEq.respectTransparency false in
/-- Reading the transported cocycle through the ORIGINAL integral corepresentation
is the actual coefficient transformation followed by the actual resolution map. -/
theorem kummerIntegralResolution_corepresentation (M : EtaleModules.{u, 0} Λ X) (q : ℕ)
    (t : Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology ⟶
      (injectiveResolution M).cocomplex.X q) :
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    let H := etaleModuleGlobalSections.{u, 0} ℤ X
    let U := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
    let a := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
      ℤ X.smallEtaleTopology
    a.inv.app ((injectiveResolution (T.obj M)).cocomplex.X q)
      (kummerConstantRestrictionHom Λ X ≫ T.map t ≫
        (kummerRestrictedResolutionComparison Λ X M).f q) =
    U.map (H.map ((kummerRestrictedResolutionComparison Λ X M).f q))
      ((Functor.isoWhiskerRight
        (etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X) U).hom.app
        ((injectiveResolution M).cocomplex.X q)
        ((Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
          Λ X.smallEtaleTopology).inv.app ((injectiveResolution M).cocomplex.X q) t)) := by
  dsimp only
  rw [← Category.assoc, ← kummerConstantRestrictionNatTrans_apply]
  let a := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
    ℤ X.smallEtaleTopology
  have h := congrArg (fun k => k.hom
    ((kummerConstantRestrictionNatTrans Λ X).app
      ((injectiveResolution M).cocomplex.X q) t))
    (a.inv.naturality ((kummerRestrictedResolutionComparison Λ X M).f q))
  change a.inv.app _ (((kummerConstantRestrictionNatTrans Λ X).app
    ((injectiveResolution M).cocomplex.X q) t) ≫
    (kummerRestrictedResolutionComparison Λ X M).f q) = _ at h
  rw [h]
  simp only [kummerConstantRestrictionNatTrans, NatTrans.comp_app,
    Functor.whiskerLeft_app, ConcreteCategory.comp_apply]
  change ((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} ℤ) ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).map
    ((kummerRestrictedResolutionComparison Λ X M).f q))
    ((a.app _).inv ((a.app _).hom _)) = _
  rw [Iso.hom_inv_id_apply]
  rfl

end Stacks.EtaleCohomology
end
