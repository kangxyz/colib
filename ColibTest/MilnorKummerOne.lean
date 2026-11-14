/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.EtaleCohomology.MilnorKummerOne

set_option maxRecDepth 4096
-- Tests specialize the universe-lifted coefficient-forgetting Ext types.
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.EtaleCohomology.MilnorKummer
universe u
variable (k : Type u) [Field k]
variable [HasExt.{u + 1} (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})]
example : (MilnorKTheory k 1 ⧸ (0 • AddMonoidHom.id (MilnorKTheory k 1)).range) ≃+
    Stacks.Kummer.unitsModuloPowers (Spec (.of k)) 0 := milnorOneModuloUnitsEquiv k 0
example (hunit : IsUnit ((1 : ℕ) : Γ(Spec (.of k), ⊤))) :
    Function.Injective (milnorOneKummerModuleClass k 1 hunit) :=
  milnorOneKummerModuleClass_injective k 1 hunit
example (hunit : IsUnit ((6 : ℕ) : Γ(Spec (.of k), ⊤))) :
    Function.Injective (milnorOneKummerModuleClass k 6 hunit) :=
  milnorOneKummerModuleClass_injective k 6 hunit
