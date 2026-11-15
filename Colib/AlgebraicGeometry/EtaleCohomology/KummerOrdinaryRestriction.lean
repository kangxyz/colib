/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerGlobalUnitRestriction

/-! # Restriction of the original ordinary Kummer class -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe u
namespace Stacks.Kummer
open Stacks.EtaleCohomology
variable {X Y : Scheme.{u}} (g : Y ⟶ X)
variable [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the actual ordinary Kummer boundary on unit representatives. -/
theorem kummerModuleRestriction_ordinary {n : ℕ} (hn0 : n ≠ 0)
    (hX : IsUnit (n : Γ(X, ⊤))) (a : (Γ(X, ⊤))ˣ) :
    Sheaf.H.map (rootsOfUnityInverseImageComparison.{u, 0} g n) 1
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} g (rootsOfUnitySheaf.{u, 0} X n) 1
        (unitKummerClass X hn0 hX (Additive.ofMul a))) =
      unitKummerClass Y hn0 (isUnit_natCast_of_hom g hX)
        (Additive.ofMul (Units.map g.appTop.hom.toMonoidHom a)) := by
  -- Instantiate the native square first, so rewriting never has to discover
  -- the Ext composition by unfolding the entire restriction-map expression.
  have h := etaleCohomologyRestrictionMap_kummerExtClass.{u, 0, u + 1}
    g hn0 hX 0 1 rfl (globalUnitsH0Equiv.{u + 1, u, 0} X (Additive.ofMul a))
  have hh := congrArg
    (fun z : Sheaf.H.{u + 1} (multiplicativeSheaf.{u, 0} Y) 0 =>
      z.comp (kummerSequence_shortExact.{u, 0} Y hn0
        (isUnit_natCast_of_hom g hX)).extClass rfl)
    (kummerModuleRestriction_globalUnits g a)
  have hfinal := h.trans hh
  have hx : unitKummerClass X hn0 hX (Additive.ofMul a) =
      (globalUnitsH0Equiv.{u + 1, u, 0} X (Additive.ofMul a)).comp
        (kummerSequence_shortExact.{u, 0} X hn0 hX).extClass rfl := rfl
  have hy : unitKummerClass Y hn0 (isUnit_natCast_of_hom g hX)
      (Additive.ofMul (Units.map g.appTop.hom.toMonoidHom a)) =
      (globalUnitsH0Equiv.{u + 1, u, 0} Y
        (Additive.ofMul (Units.map g.appTop.hom.toMonoidHom a))).comp
        (kummerSequence_shortExact.{u, 0} Y hn0
          (isUnit_natCast_of_hom g hX)).extClass rfl := rfl
  exact (congrArg (fun z : Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, 0} X n) 1 =>
    Sheaf.H.map (rootsOfUnityInverseImageComparison.{u, 0} g n) 1
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} g
        (rootsOfUnitySheaf.{u, 0} X n) 1 z)) hx).trans (hfinal.trans hy.symm)

end Stacks.Kummer
end
