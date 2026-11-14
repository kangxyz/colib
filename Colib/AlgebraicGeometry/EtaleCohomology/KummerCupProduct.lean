/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.RootsOfUnityFlat
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerModuleClass
public import StacksFrontier.CategoryTheory.Abelian.ExtCupProduct

/-!
# Cup products of the actual Kummer module classes

The exactness of tensoring with `μ_n` supplies the native Ext cup product.
Applying it to the existing quotient Kummer classes gives a biadditive pairing
of units modulo nth powers with values in `Ext²(ℤ/n, μ_n ⊗ μ_n)`.
No Steinberg relation or factorization through Milnor K-theory is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open MonoidalCategory
universe u
attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.EtaleCohomology.isMonoidal_W_etaleModules
namespace Stacks.Kummer
variable {X : Scheme.{u}} {k : Type u} [Field k]
  (f : X ⟶ Spec (.of k)) (n : ℕ) [NeZero n] [NeZero (n : k)]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The monoidal unit is the constant coefficient module sheaf. -/
def etaleModuleUnitIsoConstant :
    𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))) ≅
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n) X.smallEtaleTopology :=
  Functor.Monoidal.εIso (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n)))

/-- The actual Ext cup product of two roots-of-unity classes. -/
def rootsOfUnityCupHom :
    Ext.{u + 1} (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))))
      (rootsOfUnityModule.{u, 0} X n) 1 →+
    Ext.{u + 1} (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))))
      (rootsOfUnityModule.{u, 0} X n) 1 →+
    Ext.{u + 1} (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))))
      (rootsOfUnityModule.{u, 0} X n ⊗ rootsOfUnityModule.{u, 0} X n) 2 := by
  have he := exact_tensorRight_rootsOfUnityModule f n
  have := he.1
  have := he.2.1
  have := he.2.2
  exact Stacks.ExtCup.cupHom (𝟙 _) (by decide : 1 + 1 = 2)

variable (hX : IsUnit (n : Γ(X, ⊤)))

/-- The original Kummer module class with the canonical monoidal-unit source. -/
def kummerModuleUnitClass : unitsModuloPowers X n →+
    Ext.{u + 1} (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))))
      (rootsOfUnityModule.{u, 0} X n) 1 :=
  ((Stacks.Sheaves.UniverseLift.extPrecompIsoAddEquiv
    (etaleModuleUnitIsoConstant (X := X) n) 1).toAddMonoidHom).comp
      (kummerModuleClassModuloPowers X n hX)

/-- The cup product of the original Kummer quotient classes, as a biadditive map. -/
@[colib_tag "COL-1227",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksFrontier/CategoryTheory/Abelian/ExtCupProduct.lean:85"
    "ingredient" "The native biadditive Ext cup product for an exact right tensor functor"]
def kummerCupModuloPowers : unitsModuloPowers X n →+ unitsModuloPowers X n →+
    Ext.{u + 1} (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))))
      (rootsOfUnityModule.{u, 0} X n ⊗ rootsOfUnityModule.{u, 0} X n) 2 :=
  AddMonoidHom.mk'
    (fun a => (rootsOfUnityCupHom f n (kummerModuleUnitClass n hX a)).comp
      (kummerModuleUnitClass n hX))
    (fun a b => by
      apply AddMonoidHom.ext
      intro c
      simp only [map_add, AddMonoidHom.comp_apply, AddMonoidHom.add_apply])

/-- Evaluation is the cup product of the two actual quotient Kummer classes. -/
theorem kummerCupModuloPowers_apply (a b : unitsModuloPowers X n) :
    kummerCupModuloPowers f n hX a b = rootsOfUnityCupHom f n
      (kummerModuleUnitClass n hX a) (kummerModuleUnitClass n hX b) := rfl

end Stacks.Kummer
end
