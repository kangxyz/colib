/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerCupProduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleExtForgetPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImageMonoidalUnit

/-! # Actual constant-source compatibility for corestriction

All source maps are the native constant and adjunction maps. The final square retains
the monoidal-unit source convention of the original Kummer class.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
universe u
namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] {X Y : Scheme.{u}} (g : Y ⟶ X)

set_option backward.isDefEq.respectTransparency false in
/-- The hom direction of the actual coefficient-forgetting constant square. -/
theorem kummerCorestrictionSource_constant_hom :
    (etaleAbelianInverseImage.{u, 0} g).map
        (etaleModuleUnderlyingAbelianConstantMap Λ X) ≫
      (etaleModuleUnderlyingAbelianInverseImageIso Λ g).hom.app
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) ≫
      (etaleModuleUnderlyingAbelian Y Λ).map
        ((etaleModuleInverseImageConstantIso.{u, 0} Λ g).hom.app
          (ModuleCat.of Λ (ULift.{u + 1} Λ))) =
    (etaleAbelianInverseImageConstantIso.{u, 0} g).hom.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫
      etaleModuleUnderlyingAbelianConstantMap Λ Y := by
  have h := congrArg
    (fun z => (etaleAbelianInverseImageConstantIso.{u, 0} g).hom.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫ z ≫
      (etaleModuleUnderlyingAbelian Y Λ).map
        ((etaleModuleInverseImageConstantIso.{u, 0} Λ g).hom.app
          (ModuleCat.of Λ (ULift.{u + 1} Λ))))
    (etaleModuleUnderlyingAbelianConstantMap_comp_inverseImageConstantIso Λ g)
  simpa only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id, Iso.hom_inv_id_app_assoc] using h.symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual module adjunction source, after forgetting and its integral
constant-source map, is the actual abelian adjunction source. -/
theorem kummerCorestrictionSource_unit_constant :
    etaleModuleUnderlyingAbelianConstantMap Λ X ≫
      (etaleModuleUnderlyingAbelian X Λ).map
        ((etaleModuleInverseImageAdj.{u, 0} Λ g).unit.app
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology)) ≫
      (etaleAbelianDirectImage.{u, 0} g).map
        ((etaleModuleUnderlyingAbelian Y Λ).map
          ((etaleModuleInverseImageConstantIso.{u, 0} Λ g).hom.app
            (ModuleCat.of Λ (ULift.{u + 1} Λ)))) =
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} g).unit.app
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
      (etaleAbelianDirectImage.{u, 0} g).map
        ((etaleAbelianInverseImageConstantIso.{u, 0} g).hom.app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
      (etaleAbelianDirectImage.{u, 0} g).map
        (etaleModuleUnderlyingAbelianConstantMap Λ Y) := by
  rw [etaleModuleUnderlyingAbelianInverseImageIso_unit']
  have hn := (etaleAbelianInverseImageDirectImageAdj.{u, 0} g).unit.naturality
    (etaleModuleUnderlyingAbelianConstantMap Λ X)
  change etaleModuleUnderlyingAbelianConstantMap Λ X ≫
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} g).unit.app _ =
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} g).unit.app _ ≫
      (etaleAbelianDirectImage.{u, 0} g).map
        ((etaleAbelianInverseImage.{u, 0} g).map
          (etaleModuleUnderlyingAbelianConstantMap Λ X)) at hn
  simp only [← Category.assoc]
  erw [hn]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]
  rw [kummerCorestrictionSource_constant_hom Λ g]

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  etaleModuleInverseImageSheafPullbackMonoidal

/-- The native constant comparison is the oplax unit of inverse image. -/
theorem kummerCorestrictionSource_constant_eq_eta (n : ℕ) :
    (etaleModuleInverseImageConstantIso.{u, 0} (ZMod n) g).hom.app
        (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))) =
      Functor.OplaxMonoidal.η (etaleModuleInverseImage.{u, 0} (ZMod n) g) := by
  apply (cancel_epi (Functor.LaxMonoidal.ε
    (etaleModuleInverseImage.{u, 0} (ZMod n) g))).1
  erw [Functor.Monoidal.ε_η, etaleModuleInverseImageMonoidal_ε]
  exact Iso.inv_hom_id_app _ _

/-- The source convention of the original Kummer unit class commutes with the
actual constant comparison; the unit isomorphisms are explicitly retained. -/
theorem kummerCorestrictionSource_unitIso_square (n : ℕ) :
    (etaleModuleInverseImage.{u, 0} (ZMod n) g).map
        (Stacks.Kummer.etaleModuleUnitIsoConstant (X := X) n).hom ≫
      (etaleModuleInverseImageConstantIso.{u, 0} (ZMod n) g).hom.app
        (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))) =
    Functor.OplaxMonoidal.η (etaleModuleInverseImage.{u, 0} (ZMod n) g) ≫
      (Stacks.Kummer.etaleModuleUnitIsoConstant (X := Y) n).hom := by
  have hX : (Stacks.Kummer.etaleModuleUnitIsoConstant (X := X) n).hom = 𝟙 _ := rfl
  have hY : (Stacks.Kummer.etaleModuleUnitIsoConstant (X := Y) n).hom = 𝟙 _ := rfl
  erw [hX, hY, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  exact kummerCorestrictionSource_constant_eq_eta g n

end Stacks.EtaleCohomology
end
