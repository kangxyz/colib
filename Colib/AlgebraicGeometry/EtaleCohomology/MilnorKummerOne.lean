/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKDegreeOne
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerModuleClass

/-!
# The actual degree-one Milnor Kummer class

Transport native degree-one Milnor symbols to the literal global units of `Spec k`.
Their quotient by multiples maps by the original Kummer boundary to native module Ext.
This does not assert agreement with the independent motivic comparison or higher cups.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.EtaleCohomology.MilnorKummer

variable (k : Type u) [Field k]

/-- The native first Milnor group is the actual global-unit group of the affine field. -/
def milnorOneGlobalUnitsEquiv : MilnorKTheory k 1 ≃+ Additive (Γ(Spec (.of k), ⊤))ˣ :=
  (milnorKTheoryOneAddEquiv k).trans
    (Units.mapEquiv (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.toMulEquiv).toAdditive

/-- The equivalence carries the literal subgroup of multiples to actual unit powers. -/
theorem milnorOneGlobalUnitsEquiv_map_multiples (n : ℕ) :
    ((n • AddMonoidHom.id (MilnorKTheory k 1)).range).map
      (milnorOneGlobalUnitsEquiv k).toAddMonoidHom =
      Stacks.Kummer.unitMultiples (Spec (.of k)) n := by
  ext a
  change (∃ x, (∃ y, n • y = x) ∧ milnorOneGlobalUnitsEquiv k x = a) ↔
    ∃ b, n • b = a
  constructor
  · rintro ⟨x, ⟨y, rfl⟩, h⟩
    exact ⟨milnorOneGlobalUnitsEquiv k y, by simpa only [map_nsmul] using h⟩
  · rintro ⟨b, rfl⟩
    exact ⟨n • (milnorOneGlobalUnitsEquiv k).symm b, ⟨_, rfl⟩, by simp⟩

/-- The original Milnor quotient in weight one is the original global-unit quotient. -/
def milnorOneModuloUnitsEquiv (n : ℕ) :
    (MilnorKTheory k 1 ⧸ (n • AddMonoidHom.id (MilnorKTheory k 1)).range) ≃+
      Stacks.Kummer.unitsModuloPowers (Spec (.of k)) n :=
  QuotientAddGroup.congr _ _ (milnorOneGlobalUnitsEquiv k)
    (milnorOneGlobalUnitsEquiv_map_multiples k n)

variable (n : ℕ) [NeZero n]
  [HasExt.{u + 1} (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})]
  (hunit : IsUnit (n : Γ(Spec (.of k), ⊤)))

/-- The degree-one Milnor quotient class, defined by the actual module Kummer boundary. -/
@[colib_tag "COL-1227",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksFrontier/AlgebraicGeometry/Chow/KeyLemma/MilnorKDegreeOne.lean:133-155"
    "ingredient" "The native degree-one Milnor equivalence with actual field units",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksFrontier/AlgebraicGeometry/EtaleCohomology/KummerTheory/CohomologySequence.lean"
    "ingredient" "The actual Kummer boundary, transported without a new roots-of-unity model"]
def milnorOneKummerModuleClass :
    (MilnorKTheory k 1 ⧸ (n • AddMonoidHom.id (MilnorKTheory k 1)).range) →+
    (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n)
      (Spec (.of k)).smallEtaleTopology) 1).obj
        (Stacks.Kummer.rootsOfUnityModule.{u, 0} (Spec (.of k)) n) :=
  (Stacks.Kummer.kummerModuleClassModuloPowers (Spec (.of k)) n hunit).comp
    (milnorOneModuloUnitsEquiv k n).toAddMonoidHom

/-- The actual degree-one Milnor Kummer map is injective. -/
@[colib_tag "COL-1227"]
theorem milnorOneKummerModuleClass_injective :
    Function.Injective (milnorOneKummerModuleClass k n hunit) :=
  (Stacks.Kummer.kummerModuleClassModuloPowers_injective (Spec (.of k)) n hunit).comp
    (milnorOneModuloUnitsEquiv k n).injective

set_option maxRecDepth 4096 in
-- Definitional quotient transport crosses the actual coefficient-forgetting Ext equivalence.
/-- Forgetting module coefficients gives the original unit Kummer boundary on a symbol. -/
theorem milnorOneKummerModuleClass_mk (a : MilnorKTheory k 1) :
    Stacks.Kummer.rootsOfUnityModuleExtEquiv (Spec (.of k)) n 1
      (milnorOneKummerModuleClass k n hunit (QuotientAddGroup.mk a)) =
        Stacks.Kummer.unitKummerClass.{u + 1, u, 0} (Spec (.of k)) (NeZero.ne n) hunit
          (milnorOneGlobalUnitsEquiv k a) :=
  Stacks.Kummer.rootsOfUnityModuleExtEquiv_kummerModuleClass_mk
    (Spec (.of k)) n hunit (milnorOneGlobalUnitsEquiv k a)

end AlgebraicGeometry.EtaleCohomology.MilnorKummer
