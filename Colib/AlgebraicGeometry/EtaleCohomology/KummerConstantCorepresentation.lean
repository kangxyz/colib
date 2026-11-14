/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOriginalStandardComparison

/-!
# The actual coefficient restriction on corepresented global sections

Construct the source map from the existing underived comparison and corepresentations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
universe u
attribute [local instance] HasDerivedCategory.standard
namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- The actual coefficient restriction on global sections, read through the existing
constant-source corepresentations. This is not a comparison assumed in positive degree. -/
def kummerConstantRestrictionNatTrans :
    preadditiveCoyoneda.obj (op
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology)) ⟶
    etaleModuleRestrictScalars (Int.castRingHom Λ) X ⋙
      preadditiveCoyoneda.obj (op
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf ℤ X.smallEtaleTopology)) :=
  (Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
    Λ X.smallEtaleTopology).inv ≫
  (Functor.isoWhiskerRight
    (etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X)
    (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})).hom ≫
  Functor.whiskerLeft (etaleModuleRestrictScalars (Int.castRingHom Λ) X)
    (Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
      ℤ X.smallEtaleTopology).hom

/-- The canonical integral-to-restricted constant source map, read from the actual
coefficient comparison at the identity. Its equality to a separately defined constant
sheaf map is NOT presumed. -/
def kummerConstantRestrictionHom :
    Stacks.Cohomology.GlobalSections.constantModuleSheaf ℤ X.smallEtaleTopology ⟶
    (etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) :=
  (kummerConstantRestrictionNatTrans Λ X).app
    (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) (𝟙 _)

/-- The actual corepresentation transformation acts by the constructed source map
followed by the exact restricted morphism. -/
theorem kummerConstantRestrictionNatTrans_apply
    {M : EtaleModules.{u, 0} Λ X}
    (f : Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology ⟶ M) :
    (kummerConstantRestrictionNatTrans Λ X).app M f =
      kummerConstantRestrictionHom Λ X ≫
        (etaleModuleRestrictScalars (Int.castRingHom Λ) X).map f := by
  have h := congrArg (fun k => k.hom
    (𝟙 (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology)))
    ((kummerConstantRestrictionNatTrans Λ X).naturality f)
  change (kummerConstantRestrictionNatTrans Λ X).app M ((𝟙 _) ≫ f) =
    kummerConstantRestrictionHom Λ X ≫
      (etaleModuleRestrictScalars (Int.castRingHom Λ) X).map f at h
  simpa only [Category.id_comp] using h

end Stacks.EtaleCohomology
end
