/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerGlobalUnitTrace

/-! # Actual abelian trace of the original Kummer boundary

The constant-source adjunction morphism is retained in
all degrees. This does not identify the source with a module monoidal unit.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe u
namespace Stacks.EtaleCohomology
open Stacks.Kummer
variable {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g] [IsFinite g]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- Actual constant-source abelian corestriction on the roots-of-unity sheaf.
Its source arrow is the inverse-image adjunction unit followed by the direct
image of the canonical constant-sheaf comparison, in every degree. -/
def kummerAbelianTraceCorestriction (n q : ℕ)
    (x : Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, 0} Y n) q) :
    Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, 0} X n) q :=
  ((Ext.mk₀ (kummerH0PushSource g)).comp
      (x.mapExactFunctor (etaleAbelianDirectImage.{u, 0} g)) (zero_add q)).comp
    (Ext.mk₀ (finiteEtaleRootsOfUnityTrace g n)) (add_zero q)

set_option backward.isDefEq.respectTransparency false in
/-- The genuine Kummer boundary commutes with the actual abelian trace,
including the constant-source direct-image map. -/
theorem kummerAbelianTraceCorestriction_boundary
    {n : ℕ} (hn0 : n ≠ 0) (hX : IsUnit (n : Γ(X, ⊤)))
    (x : Sheaf.H.{u + 1} (multiplicativeSheaf.{u, 0} Y) 0) :
    kummerAbelianTraceCorestriction g n 1
        (kummerδ Y hn0 (isUnit_natCast_of_hom g hX) 0 x) =
      kummerδ X hn0 hX 0
        (Sheaf.H.map (finiteEtaleMultiplicativeTrace g) 0
          (kummerH0Push g (multiplicativeSheaf.{u, 0} Y) x)) := by
  change
    ((Ext.mk₀ (kummerH0PushSource g)).comp
        ((x.comp
          (kummerSequence_shortExact.{u, 0} Y hn0
            (isUnit_natCast_of_hom g hX)).extClass (zero_add 1)).mapExactFunctor
              (etaleAbelianDirectImage.{u, 0} g)) (zero_add 1)).comp
      (Ext.mk₀ (finiteEtaleRootsOfUnityTrace g n)) (add_zero 1) =
    (((Ext.mk₀ (kummerH0PushSource g)).comp
        (x.mapExactFunctor (etaleAbelianDirectImage.{u, 0} g)) (zero_add 0)).comp
      (Ext.mk₀ (finiteEtaleMultiplicativeTrace g)) (add_zero 0)).comp
        (kummerSequence_shortExact.{u, 0} X hn0 hX).extClass (zero_add 1)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_second_deg_zero]
  rw [finiteEtaleKummerTrace_extClass g hn0 hX]

set_option backward.isDefEq.respectTransparency false in
/-- Trace of the original Kummer class of a global unit is the original Kummer
class of its actual sectionwise multiplicative trace. -/
theorem kummerAbelianTraceCorestriction_unitKummerClass
    {n : ℕ} (hn0 : n ≠ 0) (hX : IsUnit (n : Γ(X, ⊤))) (t : Γ(Y, ⊤)ˣ) :
    kummerAbelianTraceCorestriction g n 1
        (unitKummerClass Y hn0 (isUnit_natCast_of_hom g hX) (Additive.ofMul t)) =
      unitKummerClass X hn0 hX (Additive.ofMul
        (finiteEtaleMultiplicativeTraceUnits g (Scheme.Etale.mk (𝟙 X)) t)) := by
  change kummerAbelianTraceCorestriction g n 1
      (kummerδ Y hn0 (isUnit_natCast_of_hom g hX) 0
        (globalUnitsH0Equiv Y (Additive.ofMul t))) =
    kummerδ X hn0 hX 0
      (globalUnitsH0Equiv X (Additive.ofMul
        (finiteEtaleMultiplicativeTraceUnits g (Scheme.Etale.mk (𝟙 X)) t)))
  rw [kummerAbelianTraceCorestriction_boundary, kummerH0_trace_globalUnit]

end Stacks.EtaleCohomology
end
