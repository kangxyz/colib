/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerConstantTerminalValue

/-!
# The literal constant-source map under the constant sheaf adjunction

Use the exact expression from the existing underlying-abelian constant map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] HasDerivedCategory.standard
private lemma cancelOuterIdentities {A : Type*} [Category* A]
    {V₀ V₁ V₂ : A} {i : V₀ ⟶ V₀} {j : V₂ ⟶ V₂}
    {e : V₀ ⟶ V₁} {f : V₁ ⟶ V₂} {g : V₀ ⟶ V₂}
    (hi : i = 𝟙 _) (hj : j = 𝟙 _) (h : (i ≫ e) ≫ f = g ≫ j) : e ≫ f = g := by
  simpa only [hi, hj, Category.id_comp, Category.comp_id] using h

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})
local instance : X.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  ModuleSheaf.preservesSheafification_forget₂.{u + 1} Λ X.smallEtaleTopology

/-- **The map `ℤ_X ⟶ U Λ_X` followed by `U a`**, for `a : Λ_X ⟶ M`, is adjoint to the composite
of `ℤ ⟶ Λ` with the section `Λ ⟶ M(T)` adjoint to `a`, over any final object `T` of the site. -/
theorem kummerForgetConstantAdjunction {T : X.Etale} (hT : IsTerminal T)
    (b : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        (ModuleCat.of Λ (ULift.{u + 1} Λ)))
    {M : EtaleModules.{u, 0} Λ X}
    (a : Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology ⟶ M) :
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map b ≫
        (Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} Λ
          X.smallEtaleTopology).inv.app (ModuleCat.of Λ (ULift.{u + 1} Λ))) ≫
      (etaleModuleUnderlyingAbelian X Λ).map a =
      ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} hT).homEquiv
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
        ((etaleModuleUnderlyingAbelian X Λ).obj M)).symm
        (b ≫ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
          ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT).homEquiv _ _ a)) := by
  set ā := (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT).homEquiv _ _ a
  have ha : ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT).homEquiv _
      _).symm ā = a :=
    Equiv.symm_apply_apply _ _
  rw [Adjunction.homEquiv_counit] at ha
  have hw := constantSheafAdj_counit_w X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) M hT
  have hn := (Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} Λ
    X.smallEtaleTopology).inv.naturality ā
  rw [Adjunction.homEquiv_counit, ← ha, Functor.map_comp,
    Category.assoc]
  have e : Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} Λ X.smallEtaleTopology =
      constantCommuteCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := rfl
  dsimp only [Functor.comp_map] at hn
  rw [e] at hn ⊢
  have key := ((constantCommuteCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app
      (M.obj.obj (Opposite.op T))).inv_comp_eq.2 hw.symm
  simp only [Iso.app_inv] at key
  refine (congrArg (fun t => (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
    (b) ≫ t) ((reassoc_of% hn)
      ((etaleModuleUnderlyingAbelian X Λ).map
        ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT).counit.app
      M))).symm).trans ?_
  refine (congrArg (fun t => (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
    (b) ≫ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map ā) ≫ t) key).trans ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} hT).counit.app
      ((etaleModuleUnderlyingAbelian X Λ).obj M))
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map_comp _ _).symm)

/-- Forgetting the integral adjoint of the constructed source map gives exactly
precomposition by the literal additive map `n ↦ n • 1`. -/
theorem kummerConstantRestriction_adjoint_forget :
    (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).map
      ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} ℤ)
        terminalIsTerminal).homEquiv _ _ (kummerConstantRestrictionHom Λ X)) =
    AddCommGrpCat.ofHom ((zmultiplesHom (ULift.{u + 1} Λ) 1).comp
      AddEquiv.ulift.toAddMonoidHom) ≫
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
      ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
        terminalIsTerminal).homEquiv _ _
        (𝟙 (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology))) := by
  have hone := (kummerCorepresentation_terminal_value ℤ X
    (kummerConstantRestrictionHom Λ X)).symm.trans
      ((kummerConstantRestriction_terminal_section Λ X).trans
        (kummerCorepresentation_terminal_value Λ X (𝟙 _)))
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  rintro ⟨n⟩
  change ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} ℤ)
    terminalIsTerminal).homEquiv _ _ (kummerConstantRestrictionHom Λ X)).hom (ULift.up n) =
    ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      terminalIsTerminal).homEquiv _ _
      (𝟙 (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology))).hom
        (n • (1 : ULift.{u + 1} Λ))
  have hn : (ULift.up n : ULift.{u + 1} ℤ) = n • (ULift.up 1 : ULift.{u + 1} ℤ) := by
    ext
    simp
  rw [hn, map_zsmul, map_zsmul]
  exact congrArg (fun y => n • y) hone

set_option backward.isDefEq.respectTransparency false in
/-- The source morphism constructed from the ORIGINAL corepresentations is the exact
expanded expression of the existing underlying-abelian constant map. The wrapper using
the separately imported original definition is not included here. -/
theorem kummerConstantRestriction_eq_literal :
    (etaleModuleUnderlyingAbelianConstantIso X).inv ≫
      (etaleModuleUnderlyingAbelian X ℤ).map (kummerConstantRestrictionHom Λ X) =
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      (AddCommGrpCat.ofHom ((zmultiplesHom (ULift.{u + 1} Λ) 1).comp
        AddEquiv.ulift.toAddMonoidHom)) ≫
      (Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} Λ X.smallEtaleTopology).inv.app
        (ModuleCat.of Λ (ULift.{u + 1} Λ)) := by
  have hL := kummerForgetConstantAdjunction ℤ X terminalIsTerminal (𝟙 _)
    (kummerConstantRestrictionHom Λ X)
  have hR := kummerForgetConstantAdjunction Λ X terminalIsTerminal
    (AddCommGrpCat.ofHom ((zmultiplesHom (ULift.{u + 1} Λ) 1).comp
      AddEquiv.ulift.toAddMonoidHom))
    (𝟙 (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology))
  have h := hL.trans ((congrArg
    ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).homEquiv _ _).symm
    (kummerConstantRestriction_adjoint_forget Λ X)).trans hR.symm)
  exact cancelOuterIdentities
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map_id _)
    ((etaleModuleUnderlyingAbelian X Λ).map_id _) h

end Stacks.EtaleCohomology
end
