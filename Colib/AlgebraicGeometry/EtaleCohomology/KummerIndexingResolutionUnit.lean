/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerDerivedUnitResolution
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Original comparison indexing factors

Explicit factors of the original indexing maps, without replacing the comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] HasDerivedCategory.standard
namespace Stacks.EtaleCohomology

/-- The second original indexing factor is homology of the inverse actual derived unit. -/
theorem kummerIndexingResolutionUnit (Λ : Type) [CommRing Λ] (X : Scheme.{u})
    (M : EtaleModules.{u, 0} Λ X) (i : ℤ) :
    (Stacks.DerivedIndexing.zStep₂ (etaleModuleGlobalSections.{u, 0} Λ X) i).hom.app M =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
        (inv ((etaleModuleGlobalSections.{u, 0} Λ X).rightDerivedFunctorPlusUnith.app
          (Stacks.DerivedIndexing.resPlus.obj M))) := by
  simp only [Stacks.DerivedIndexing.zStep₂, Stacks.DerivedIndexing.resDerivedIso,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, asIso_inv,
    Functor.whiskerRight_app, NatIso.isIso_inv_app,
    Functor.whiskerLeft_app]

end Stacks.EtaleCohomology
end
