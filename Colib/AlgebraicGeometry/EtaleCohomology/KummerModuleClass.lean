/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.KummerUnitsModulo
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityModule

/-!
# The Kummer quotient class in roots-of-unity module cohomology

The existing coefficient-forgetting comparison carries actual `ℤ/n`-module `Ext` out of the
constant sheaf to ordinary abelian sheaf cohomology. We use its inverse to transport the
original Kummer quotient map to the native roots-of-unity module. No primitive root is chosen,
and no trivialization of `μ_n` or cup-product comparison is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Kummer

variable (X : Scheme.{u}) (n : ℕ) [NeZero n]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- Cohomology of the native roots-of-unity module is the original abelian sheaf cohomology. -/
def rootsOfUnityModuleExtEquiv (q : ℕ) :
    (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n)
      X.smallEtaleTopology) q).obj (rootsOfUnityModule.{u, 0} X n) ≃+
        Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, 0} X n) q :=
  Stacks.EtaleCohomology.extConstantAddEquivSheafH X (rootsOfUnityModule.{u, 0} X n) q

variable (hX : IsUnit (n : Γ(X, ⊤)))

/-- The original Kummer quotient class, now in actual `ℤ/n`-module `Ext¹`. -/
@[colib_tag "COL-1227",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksFrontier/AlgebraicGeometry/EtaleCohomology/EtaleModuleRestrictScalarsCohomology.lean:148"
    "ingredient" "Native module Ext to ordinary abelian sheaf cohomology comparison",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksFrontier/AlgebraicGeometry/EtaleCohomology/KummerTheory/RootsOfUnityModule.lean:100"
    "ingredient" "The native roots-of-unity module with its coefficient-forgetting identification"]
def kummerModuleClassModuloPowers : unitsModuloPowers X n →+
    (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n)
      X.smallEtaleTopology) 1).obj (rootsOfUnityModule.{u, 0} X n) :=
  (rootsOfUnityModuleExtEquiv X n 1).symm.toAddMonoidHom.comp
    (kummerClassModuloPowers.{u + 1, u, 0} X (NeZero.ne n) hX)

set_option maxRecDepth 4096 in
/-- Forgetting module coefficients returns the original ordinary Kummer quotient map. -/
theorem rootsOfUnityModuleExtEquiv_kummerModuleClass (a : unitsModuloPowers X n) :
    rootsOfUnityModuleExtEquiv X n 1 (kummerModuleClassModuloPowers X n hX a) =
      kummerClassModuloPowers.{u + 1, u, 0} X (NeZero.ne n) hX a :=
  (rootsOfUnityModuleExtEquiv X n 1).apply_symm_apply _

/-- The module-valued class on a coset is the original boundary on its unit representative. -/
theorem rootsOfUnityModuleExtEquiv_kummerModuleClass_mk (a : Additive (Γ(X, ⊤))ˣ) :
    rootsOfUnityModuleExtEquiv X n 1
      (kummerModuleClassModuloPowers X n hX (QuotientAddGroup.mk a)) =
        unitKummerClass.{u + 1, u, 0} X (NeZero.ne n) hX a :=
  rootsOfUnityModuleExtEquiv_kummerModuleClass X n hX _

/-- The original global-unit quotient remains injective in module cohomology. -/
@[colib_tag "COL-1227"]
theorem kummerModuleClassModuloPowers_injective :
    Function.Injective (kummerModuleClassModuloPowers X n hX) :=
  (rootsOfUnityModuleExtEquiv X n 1).symm.injective.comp
    (kummerClassModuloPowers_injective.{u + 1, u, 0} X (NeZero.ne n) hX)

end Stacks.Kummer
