/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerModuleComparisonNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CocycleFormula

/-!
# The exact forgetful map on resolution cocycles

Compare the exact image of a module injective resolution to an actual injective
resolution of the underlying abelian sheaf. The exact image is not assumed injective.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe u
attribute [local instance] HasDerivedCategory.standard
namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})
local instance : (etaleModuleUnderlyingAbelian X Λ).Additive :=
  ⟨fun {_ _ _ _} => by
    ext U : 3
    exact (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map_add⟩
local instance : PreservesFiniteLimits (etaleModuleUnderlyingAbelian X Λ) :=
  inferInstanceAs (PreservesFiniteLimits
    (etaleModuleRestrictScalars (Int.castRingHom Λ) X ⋙ etaleModuleUnderlyingAbelian X ℤ))
local instance : PreservesFiniteColimits (etaleModuleUnderlyingAbelian X Λ) :=
  inferInstanceAs (PreservesFiniteColimits
    (etaleModuleRestrictScalars (Int.castRingHom Λ) X ⋙ etaleModuleUnderlyingAbelian X ℤ))

variable [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- A genuine comparison into an injective resolution of the underlying sheaf.
The forgotten resolution need only be exact, NOT termwise injective. -/
def kummerForgetResolutionComparison {M : EtaleModules.{u, 0} Λ X}
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((etaleModuleUnderlyingAbelian X Λ).obj M)) :
    ((etaleModuleUnderlyingAbelian X Λ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex ⟶ J.cocomplex :=
  Classical.choose (Stacks.Cohomology.ModuleComparison.exists_mapResolutionComparison
    (etaleModuleUnderlyingAbelian X Λ) I J)

omit [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- This chosen comparison extends the identity on the coefficient. -/
theorem kummerForgetResolutionComparison_augmentation {M : EtaleModules.{u, 0} Λ X}
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((etaleModuleUnderlyingAbelian X Λ).obj M)) :
    (etaleModuleUnderlyingAbelian X Λ).map (I.ι.f 0) ≫
      (kummerForgetResolutionComparison Λ X I J).f 0 = J.ι.f 0 :=
  Classical.choose_spec (Stacks.Cohomology.ModuleComparison.exists_mapResolutionComparison
    (etaleModuleUnderlyingAbelian X Λ) I J)


omit [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- A source morphism followed by the forgotten cocycle is closed in the actual
injective resolution of the underlying coefficient. -/
theorem kummerForgetResolution_cocycle {M A : EtaleModules.{u, 0} Λ X}
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((etaleModuleUnderlyingAbelian X Λ).obj M))
    {W : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (b : W ⟶ (etaleModuleUnderlyingAbelian X Λ).obj A)
    (q : ℕ) (t : A ⟶ I.cocomplex.X q) (ht : t ≫ I.cocomplex.d q (q + 1) = 0) :
    (b ≫ (etaleModuleUnderlyingAbelian X Λ).map t ≫
      (kummerForgetResolutionComparison Λ X I J).f q) ≫
      J.cocomplex.d q (q + 1) = 0 := by
  rw [Category.assoc]
  exact (congrArg (b ≫ ·)
    (Stacks.Cohomology.ModuleComparison.extMk_map_comp_eq_zero
      (etaleModuleUnderlyingAbelian X Λ) I J
      (kummerForgetResolutionComparison Λ X I J) t rfl ht)).trans (Limits.comp_zero)

/-- The exact forgetful functor and source precomposition on a cocycle class.
No claim that the original derived coefficient comparison equals this map is used. -/
theorem kummerForgetResolution_extMk {M A : EtaleModules.{u, 0} Λ X}
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((etaleModuleUnderlyingAbelian X Λ).obj M))
    {W : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (b : W ⟶ (etaleModuleUnderlyingAbelian X Λ).obj A)
    (q : ℕ) (t : A ⟶ I.cocomplex.X q) (ht : t ≫ I.cocomplex.d q (q + 1) = 0) :
    (Ext.mk₀ b).comp ((I.extMk t (q + 1) rfl ht).mapExactFunctor
      (etaleModuleUnderlyingAbelian X Λ)) (zero_add q) =
      J.extMk (b ≫ (etaleModuleUnderlyingAbelian X Λ).map t ≫
        (kummerForgetResolutionComparison Λ X I J).f q) (q + 1) rfl
          (kummerForgetResolution_cocycle Λ X I J b q t ht) := by
  rw [Stacks.Cohomology.ModuleComparison.mapExactFunctor_extMk
      (etaleModuleUnderlyingAbelian X Λ) I J
      (kummerForgetResolutionComparison Λ X I J)
      (kummerForgetResolutionComparison_augmentation Λ X I J),
    InjectiveResolution.mk₀_comp_extMk]

end Stacks.EtaleCohomology
end
