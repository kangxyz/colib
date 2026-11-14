/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Monoidal.LeftAdjointUniqMonoidalOfUnit
public import Colib.CategoryTheory.Sites.SheafPushforwardNatTransMonoidal
public import Colib.CategoryTheory.Sites.SheafPullbackNativeAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImageMonoidal
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage

/-!
# The native module inverse-image to restriction comparison is monoidal

The restriction structure is its canonical
pushforward lax structure. The inverse-image structure is the original native
Kan-extension/localization one, not a replacement structure.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ] {Y X : Scheme.{u}} (g : Y ⟶ X) [Etale g]

/-- The existing restriction adjunction has the original site-induced unit. -/
theorem etaleModuleRestrictionDirectImageAdj_unit_eq :
    (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ g).unit =
      ((Scheme.Etale.smallEtaleComposeBaseChangeAdj g).sheafPushforwardContinuous
        (E := ModuleCat.{u + 1} Λ) Y.smallEtaleTopology X.smallEtaleTopology).unit := by
  ext M U a
  rfl

local instance : HasColimitsOfSize.{u + 1, u + 1, u + 1, u + 2}
    (ModuleCat.{u + 1, 0} Λ) :=
  ModuleCat.hasColimitsOfSize.{u + 1, 0, u + 1, u + 1} Λ

attribute [local instance] Sheaf.monoidalCategory
  Stacks.SheafPushforwardMonoidal.pushforwardLaxMonoidal
  etaleModuleInverseImageSheafPullbackMonoidal
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorLeft
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorRight

variable [(X.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal]
  [(Y.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal]

/-- The actual restriction adjunction unit is monoidal for canonical lax tensorators. -/
theorem etaleModuleRestrictionDirectImageAdj_unit_isMonoidal :
    (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ g).unit.IsMonoidal := by
  rw [etaleModuleRestrictionDirectImageAdj_unit_eq]
  exact Colib.SheafPushforwardMonoidal.sheafPushforwardAdjunction_unit_isMonoidal
    Y.smallEtaleTopology X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (Scheme.Etale.smallEtaleComposeBaseChangeAdj g)

omit [Etale g] in
/-- The native module inverse-image adjunction is monoidal for its original structure. -/
theorem etaleModuleInverseImageAdj_native_isMonoidal :
    (etaleModuleInverseImageAdj.{u, 0} Λ g).IsMonoidal := by
  have : ∀ Z : Y.Etaleᵒᵖ,
      IsFiltered (CostructuredArrow (smallEtaleBaseChange g).op Z) :=
    fun Z => IsFiltered.of_equivalence
      (structuredArrowOpEquivalence (smallEtaleBaseChange g) (Opposite.unop Z))
  have : ∀ (Z : Y.Etaleᵒᵖ) (M : ModuleCat.{u + 1} Λ),
      PreservesColimitsOfShape (CostructuredArrow (smallEtaleBaseChange g).op Z)
        ((curriedTensor (ModuleCat.{u + 1} Λ)).obj M) :=
    fun _ M => inferInstanceAs (PreservesColimitsOfShape _ (tensorLeft M))
  have : ∀ (Z : Y.Etaleᵒᵖ) (M : ModuleCat.{u + 1} Λ),
      PreservesColimitsOfShape (CostructuredArrow (smallEtaleBaseChange g).op Z)
        ((curriedTensor (ModuleCat.{u + 1} Λ)).flip.obj M) := by
    intro Z M
    have : PreservesColimitsOfSize.{u, u + 1} (tensorRight M) :=
      preservesColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} (tensorRight M)
    infer_instance
  exact Colib.SheafPullbackCoherence.nativeSheafAdjunction_isMonoidal
    (smallEtaleBaseChange g) (ModuleCat.{u + 1} Λ)
    X.smallEtaleTopology Y.smallEtaleTopology

/-- The existing inverse-image/restriction comparison respects the canonical tensorators. -/
theorem etaleModuleInverseImageRestrictionIso_hom_isMonoidal :
    (etaleModuleInverseImageRestrictionIso.{u, 0} Λ g).hom.IsMonoidal := by
  have := etaleModuleInverseImageAdj_native_isMonoidal Λ g
  have := etaleModuleRestrictionDirectImageAdj_unit_isMonoidal Λ g
  exact Colib.MonoidalAdjunction.leftAdjointUniq_isMonoidal_of_unit
    (etaleModuleInverseImageAdj.{u, 0} Λ g)
    (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ g)

/-- The concrete tensor square for the original inverse-image/restriction comparison. -/
theorem etaleModuleInverseImageRestrictionIso_hom_tensor
    (A M : EtaleModules.{u, 0} Λ X) :
    Functor.LaxMonoidal.μ (etaleModuleInverseImage.{u, 0} Λ g) A M ≫
        (etaleModuleInverseImageRestrictionIso.{u, 0} Λ g).hom.app (A ⊗ M) =
      ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ g).hom.app A ⊗ₘ
        (etaleModuleInverseImageRestrictionIso.{u, 0} Λ g).hom.app M) ≫
          Functor.LaxMonoidal.μ (etaleModuleRestriction.{u, 0} Λ g) A M := by
  have := etaleModuleInverseImageRestrictionIso_hom_isMonoidal Λ g
  exact NatTrans.IsMonoidal.tensor (τ :=
    (etaleModuleInverseImageRestrictionIso.{u, 0} Λ g).hom) A M

end Stacks.EtaleCohomology
