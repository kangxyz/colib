/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerConstantCorepresentation

/-!
# Terminal values of the original constant-source comparison
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] HasDerivedCategory.standard

private lemma adjunctionComparisonHom {A B : Type*} [Category* A] [Category* B]
    {F : A ⥤ B} {G G' : B ⥤ A} (a : F ⊣ G) (b : F ⊣ G')
    {V : A} {W : B} (f : F.obj V ⟶ W) :
    a.homEquiv V W f ≫ (a.rightAdjointUniq b).hom.app W = b.homEquiv V W f := by
  simp only [Adjunction.homEquiv_unit]
  rw [Category.assoc, (a.rightAdjointUniq b).hom.naturality,
    ← Category.assoc, Adjunction.unit_rightAdjointUniq_hom_app]

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- The original corepresentation, evaluated at the terminal object, is the literal
constant-sheaf adjunction evaluated on the element one. -/
theorem kummerCorepresentation_terminal_value
    {M : EtaleModules.{u, 0} Λ X}
    (f : Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology ⟶ M) :
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) terminalIsTerminal).hom.app M
      ((Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
        Λ X.smallEtaleTopology).inv.app M f) =
    ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      terminalIsTerminal).homEquiv _ M f) (ULift.up (1 : Λ)) := by
  have h := adjunctionComparisonHom
    (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) terminalIsTerminal) f
  exact congrArg (fun k => k.hom (ULift.up (1 : Λ))) h

/-- Under the terminal global-sections identification, the constructed integral source
map picks the section given by the identity of the original constant module sheaf. -/
theorem kummerConstantRestriction_terminal_section :
    let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
      (ModuleCat.{u + 1} ℤ) terminalIsTerminal).hom.app (T.obj C)
      ((Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
        ℤ X.smallEtaleTopology).inv.app (T.obj C) (kummerConstantRestrictionHom Λ X)) =
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) terminalIsTerminal).hom.app C
      ((Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
        Λ X.smallEtaleTopology).inv.app C (𝟙 C)) := by
  dsimp only
  let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let e := (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
    (ModuleCat.{u + 1} ℤ) terminalIsTerminal).app (T.obj C)
  let a := (Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
    ℤ X.smallEtaleTopology).app (T.obj C)
  change e.hom (a.inv (a.hom (e.inv _))) = _
  rw [Iso.hom_inv_id_apply]
  exact Iso.inv_hom_id_apply e _

/-- The constructed source morphism sends integral one to the canonical constant section one. -/
theorem kummerConstantRestriction_one :
    ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} ℤ)
      terminalIsTerminal).homEquiv _ _ (kummerConstantRestrictionHom Λ X))
        (ULift.up (1 : ℤ)) =
    ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      terminalIsTerminal).unit.app (ModuleCat.of Λ (ULift.{u + 1} Λ)))
        (ULift.up (1 : Λ)) := by
  have h := (kummerCorepresentation_terminal_value ℤ X
    (kummerConstantRestrictionHom Λ X)).symm.trans
      ((kummerConstantRestriction_terminal_section Λ X).trans
        (kummerCorepresentation_terminal_value Λ X (𝟙 _)))
  have hunit :
      (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
        terminalIsTerminal).homEquiv _ _
          (𝟙 (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology)) =
      (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
        terminalIsTerminal).unit.app (ModuleCat.of Λ (ULift.{u + 1} Λ)) := by
    rw [Adjunction.homEquiv_unit]
    exact (congrArg (fun f =>
      (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
        terminalIsTerminal).unit.app (ModuleCat.of Λ (ULift.{u + 1} Λ)) ≫ f)
      (((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (Opposite.op (⊤_ X.Etale))).map_id _)).trans (Category.comp_id _)
  exact h.trans (congrArg (fun k => k.hom (ULift.up (1 : Λ))) hunit)

end Stacks.EtaleCohomology
end
