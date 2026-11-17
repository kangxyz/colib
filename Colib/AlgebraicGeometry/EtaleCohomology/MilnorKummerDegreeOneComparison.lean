/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.OrderedMilnorKummer
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKDegreeOne

/-!
# The ordinary all-degree symbol retains the original degree-one Kummer boundary

Normalize the native tensor power by its left unitor. The result is exactly the
original unit Kummer class on the units given by the native first Milnor group.
This is a comparison of existing symbols, not an assertion about motivic realization.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MonoidalCategory
universe u
set_option maxRecDepth 4096
attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.EtaleCohomology.isMonoidal_W_etaleModules

namespace AlgebraicGeometry.EtaleCohomology.MilnorKummer

variable (k : Type u) [Field k]

/-- Native degree-one tuples are the inverse of the original units equivalence. -/
theorem milnorKTupleSymbol_one_eq (a : Fin 1 → kˣ) :
    milnorKTupleSymbol a = (milnorKTheoryOneAddEquiv k).symm (Additive.ofMul (a 0)) := by
  apply Subtype.ext
  simp only [coe_milnorKTupleSymbol, List.ofFn_succ, List.ofFn_zero,
    milnorKSymbolProd_singleton, coe_milnorKTheoryOneAddEquiv_symm, milnorKSymbol_eq_mk']

variable (n : ℕ) [NeZero n] [NeZero (n : k)]
  [HasExt.{u + 1} (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The all-degree symbol in degree one is the unchanged native Kummer boundary. -/
@[colib_tag "COL-1300"]
theorem milnorKummerSymbol_one (x : MilnorKTheory k 1) :
    (milnorKummerSymbol k n 1 x).comp
        (Ext.mk₀ (λ_ (Stacks.Kummer.rootsOfUnityModule.{u, 0} (Spec (.of k)) n)).hom)
        (by decide : 1 + 0 = 1) =
      Stacks.Kummer.kummerModuleUnitClass n (fieldKummerInvertibility k n)
        (fieldUnitModuloPowers k n (milnorKTheoryOneAddEquiv k x)) := by
  let a : Fin 1 → kˣ := fun _ => (milnorKTheoryOneAddEquiv k x).toMul
  have hx : milnorKTupleSymbol a = x := by
    rw [milnorKTupleSymbol_one_eq]
    exact (milnorKTheoryOneAddEquiv k).symm_apply_apply x
  rw [← hx, milnorKummerSymbol_tuple]
  have he : milnorKTheoryOneAddEquiv k (milnorKTupleSymbol a) = Additive.ofMul (a 0) := by
    rw [milnorKTupleSymbol_one_eq, AddEquiv.apply_symm_apply]
  rw [he]
  exact Stacks.Kummer.orderedKummerCup_one _ _ _ _

/-- The quotient map retains the original boundary on degree-one representatives. -/
theorem milnorModuloKummerSymbol_one_mk (x : MilnorKTheory k 1) :
    (milnorModuloKummerSymbol k n 0 (QuotientAddGroup.mk x)).comp
        (Ext.mk₀ (λ_ (Stacks.Kummer.rootsOfUnityModule.{u, 0} (Spec (.of k)) n)).hom)
        (by decide : 1 + 0 = 1) =
      Stacks.Kummer.kummerModuleUnitClass n (fieldKummerInvertibility k n)
        (fieldUnitModuloPowers k n (milnorKTheoryOneAddEquiv k x)) :=
  milnorKummerSymbol_one k n x

/-- Forgetting native module coefficients recovers the original ordinary unit boundary. -/
theorem milnorKummerSymbol_one_unitKummerClass (x : MilnorKTheory k 1) :
    Stacks.Kummer.rootsOfUnityModuleExtEquiv (Spec (.of k)) n 1
      ((Stacks.Sheaves.UniverseLift.extPrecompIsoAddEquiv
        (Stacks.Kummer.etaleModuleUnitIsoConstant (X := Spec (.of k)) n) 1).symm
        ((milnorKummerSymbol k n 1 x).comp
          (Ext.mk₀ (λ_ (Stacks.Kummer.rootsOfUnityModule.{u, 0} (Spec (.of k)) n)).hom)
          (by decide : 1 + 0 = 1))) =
      Stacks.Kummer.unitKummerClass.{u + 1, u, 0} (Spec (.of k)) (NeZero.ne n)
        (fieldKummerInvertibility k n)
        ((Units.map (Scheme.ΓSpecIso (.of k)).inv.hom.toMonoidHom).toAdditive
          (milnorKTheoryOneAddEquiv k x)) := by
  rw [milnorKummerSymbol_one]
  change Stacks.Kummer.rootsOfUnityModuleExtEquiv _ _ _
    ((Stacks.Sheaves.UniverseLift.extPrecompIsoAddEquiv _ _).symm
      ((Stacks.Sheaves.UniverseLift.extPrecompIsoAddEquiv _ _)
        (Stacks.Kummer.kummerModuleClassModuloPowers _ _ _ _))) = _
  rw [AddEquiv.symm_apply_apply]
  exact Stacks.Kummer.rootsOfUnityModuleExtEquiv_kummerModuleClass_mk _ _ _ _

end AlgebraicGeometry.EtaleCohomology.MilnorKummer
end
