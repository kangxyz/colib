/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOriginalExtFunctoriality
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerModuleComparisonNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RestrictionDegreeZero
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerCorestrictionSource
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerRootsOfUnityTraceCompatibility

/-! # Restriction of the original module-valued Kummer classes

The original Kummer quotient and unit-source classes are retained.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory AlgebraicGeometry
universe u
attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.EtaleCohomology.isMonoidal_W_etaleModules
  Stacks.EtaleCohomology.etaleModuleInverseImageSheafPullbackMonoidal
  Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteLimits
  Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteColimits
namespace Stacks.Kummer
open Stacks.EtaleCohomology
variable {X Y : Scheme.{u}} (g : Y ⟶ X)
variable [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the original global-unit class at any canonical terminal witness. -/
theorem kummerRestriction_equiv₀_globalUnits
    (Z : Scheme.{u}) [HasExt.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hT : IsTerminal (Scheme.Etale.mk (𝟙 Z))) (a : Γ(Z, ⊤)ˣ) :
    Sheaf.H.equiv₀ (multiplicativeSheaf.{u, 0} Z) hT
      (globalUnitsH0Equiv Z (Additive.ofMul a)) =
        ofUnit.{u, 0} (U := Scheme.Etale.mk (𝟙 Z)) a := by
  simp only [globalUnitsH0Equiv, AddEquiv.coe_mk, Equiv.coe_fn_mk]
  let : MorphismProperty.ContainsIdentities (@Etale.{u}) := ⟨fun _ => inferInstance⟩
  have hterm : hT = MorphismProperty.Over.mkIdTerminal (@Etale.{u}) Z :=
    Subsingleton.elim _ _
  erw [hterm, AddEquiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Existing H0 pullback naturality, read through the original global-unit equivalence. -/
theorem kummerModuleRestriction_globalUnits (a : (Γ(X, ⊤))ˣ) :
    Sheaf.H.map (multiplicativeInverseImageComparison.{u, 0} g) 0
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} g (multiplicativeSheaf.{u, 0} X) 0
        (globalUnitsH0Equiv X (Additive.ofMul a))) =
      globalUnitsH0Equiv Y (Additive.ofMul (Units.map g.appTop.hom.toMonoidHom a)) := by
  -- Adapted from Stacks.EtaleCohomology.KummerFlag.unitH0Class_restriction,
  -- but at coefficient universe 0 and directly on the original globalUnitsH0Equiv.
  -- Only its lower degree-zero, Gm comparison and terminal-object APIs are used.
  have hx : Sheaf.H.equiv₀ (multiplicativeSheaf.{u, 0} X) (isTerminalEtaleMkId X)
      (globalUnitsH0Equiv X (Additive.ofMul a)) =
        ofUnit.{u, 0} (U := Scheme.Etale.mk (𝟙 X)) a := by
    exact kummerRestriction_equiv₀_globalUnits X _ a
  have hy : Sheaf.H.equiv₀ (multiplicativeSheaf.{u, 0} Y) (isTerminalEtaleMkId Y)
      (globalUnitsH0Equiv Y (Additive.ofMul (Units.map g.appTop.hom.toMonoidHom a))) =
        ofUnit.{u, 0} (U := Scheme.Etale.mk (𝟙 Y)) (Units.map g.appTop.hom.toMonoidHom a) := by
    exact kummerRestriction_equiv₀_globalUnits Y _ _
  apply (Sheaf.H.equiv₀ _ (isTerminalEtaleMkId Y)).injective
  rw [hy, ← Sheaf.H.equiv₀_naturality, equiv₀_etaleCohomologyRestrictionMap_zero, hx]
  set b := ((isTerminalEtaleMkId X).isTerminalObj (smallEtaleBaseChange g)).from
    (Scheme.Etale.mk (𝟙 Y))
  have h3 := ConcreteCategory.congr_hom
    ((multiplicativeInverseImageComparison.{u, 0} g).hom.naturality b.op)
    (((etaleAbelianInverseImageDirectImageAdj.{u, 0} g).unit.app
      (multiplicativeSheaf.{u, 0} X)).hom.app (Opposite.op (Scheme.Etale.mk (𝟙 X)))
        (ofUnit.{u, 0} (U := Scheme.Etale.mk (𝟙 X)) a))
  refine h3.trans ((ConcreteCategory.comp_apply _ _ _).trans ?_)
  refine (congrArg (ConcreteCategory.hom
    ((multiplicativeSheaf.{u, 0} Y).obj.map b.op))
    (multiplicativeInverseImageComparison_app_ofUnit.{u, 0} g
      (Scheme.Etale.mk (𝟙 X)) a)).trans ?_
  refine (map_ofUnit.{u, 0} b _).trans ?_
  have hb : b.left ≫ pullback.fst (Scheme.Etale.mk (𝟙 X)).hom g = g := by
    have hw : b.left ≫ pullback.snd (Scheme.Etale.mk (𝟙 X)).hom g = 𝟙 Y :=
      MorphismProperty.Over.w b
    have hc : pullback.fst (Scheme.Etale.mk (𝟙 X)).hom g =
        pullback.snd (Scheme.Etale.mk (𝟙 X)).hom g ≫ g :=
      (Category.comp_id _).symm.trans pullback.condition
    refine (congrArg (fun h => b.left ≫ h) hc).trans ?_
    change (b.left ≫ pullback.snd (Scheme.Etale.mk (𝟙 X)).hom g) ≫ g = g
    rw [hw]
    exact Category.id_comp g
  congr 1
  ext
  change b.left.appTop.hom ((pullback.fst (Scheme.Etale.mk (𝟙 X)).hom g).appTop.hom _) =
    g.appTop.hom _
  exact congrArg (fun f : Y ⟶ X => f.appTop.hom (a : Γ(X, ⊤))) hb

end Stacks.Kummer
end
