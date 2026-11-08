/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Additivity.CompactCoproductSeparationNaturality
public import ColibTest.CompactCoproductChangeWeak

/-! # Whole change-weak separation with both actual endpoint casts -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory.Waldhausen.Product SSet
open CategoryTheory CategoryTheory.Limits Topology CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Additivity CategoryTheory.Waldhausen.Fibration
open scoped Topology
universe u v
namespace ColibTest.CompactCoproductSeparationNaturality
variable {C : Type u} [Category.{v} C] (W : Structure C)
  (N : NestedWeakEquivalences W) [HasBinaryCoproducts C] (n : ℕ)

/-- Both complete old unit cylinders retain the original change-weak map. -/
theorem original_unit_cylinders (s t : unitInterval) (x : W.Delooping) :
    changeWeakMap N (coproductLeftUnitHomotopy W (s, x)) =
      coproductLeftUnitHomotopy N.coarse (s, changeWeakMap N x) ∧
    changeWeakMap N (coproductRightUnitHomotopy W (t, x)) =
      coproductRightUnitHomotopy N.coarse (t, changeWeakMap N x) :=
  ⟨coproductLeftUnitHomotopy_changeWeak W N s x,
    coproductRightUnitHomotopy_changeWeak W N t x⟩

/-- Every separation time survives with an independently varying original input cube. -/
theorem original_independent_times
    (P : C(unitInterval, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint))
    (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) (s t : unitInterval) :
    coproductChangeWeakCubeMap W N n (coproductSeparationPath n W (P s) q t) =
      coproductSeparationPath n N.coarse (coproductChangeWeakCubeMap W N n (P s))
        (coproductChangeWeakCubeMap W N n q) t :=
  coproductSeparationPath_changeWeak_apply W N n (P s) q t

/-- The whole path comparison retains both source and target endpoint casts. -/
theorem original_endpoint_casts
    (p q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    ((coproductSeparationPath n W p q).map (coproductChangeWeakCubeMap W N n).continuous).cast
      (coproductCube_changeWeak W N n p q).symm
      (coproductChangeWeakCubeMap_transAt W N n q p).symm =
        coproductSeparationPath n N.coarse (coproductChangeWeakCubeMap W N n p)
          (coproductChangeWeakCubeMap W N n q) :=
  coproductSeparationPath_changeWeak W N n p q

omit [HasBinaryCoproducts C] in
/-- The original supplied null path is unchanged pointwise by its explicit target cast. -/
theorem original_null_time
    {c : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint}
    (P : Path c GenLoop.const) (t : unitInterval) :
    coproductChangeWeakNullPath W N n P t = coproductChangeWeakCubeMap W N n (P t) := rfl

/-- Degree zero retains the original q-first order at every separation time. -/
theorem original_degree_zero
    (p q : GenLoop (Fin (0 + 1)) W.Delooping W.kBasepoint) (t : unitInterval) :
    coproductChangeWeakCubeMap W N 0 (coproductSeparationPath 0 W p q t) =
      coproductSeparationPath 0 N.coarse (coproductChangeWeakCubeMap W N 0 p)
        (coproductChangeWeakCubeMap W N 0 q) t :=
  coproductSeparationPath_changeWeak_apply W N 0 p q t

end ColibTest.CompactCoproductSeparationNaturality
