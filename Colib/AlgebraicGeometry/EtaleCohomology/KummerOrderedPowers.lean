/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.KummerCupProduct
public import StacksFrontier.CategoryTheory.Monoidal.TensorPow

/-!
# Ordered Kummer cups in all nonnegative degrees

Use the native tensor powers of the roots-of-unity module and the original Ext cup.
The empty symbol is the identity of the monoidal unit. Successors append the last
Kummer class. This is an ordered cup construction, not yet a descent to Milnor K-theory.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MonoidalCategory
universe u
set_option maxRecDepth 4096
attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.EtaleCohomology.isMonoidal_W_etaleModules
namespace Stacks.Kummer
variable {X : Scheme.{u}} {k : Type u} [Field k]
  (f : X ⟶ Spec (.of k)) (n : ℕ) [NeZero n] [NeZero (n : k)]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- Ordinary Ext with the native tensor-power coefficient, without a Tate identification. -/
abbrev rootsOfUnityPowerTarget (q : ℕ) :=
  Ext.{u + 1} (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))))
    (tensorPow (rootsOfUnityModule.{u, 0} X n) q) q

/-- Append a degree-one roots-of-unity class using the actual cup product. -/
def rootsOfUnityPowerCupHom (q : ℕ) :
    rootsOfUnityPowerTarget (X := X) n q →+
    Ext.{u + 1} (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))))
      (rootsOfUnityModule.{u, 0} X n) 1 →+
    rootsOfUnityPowerTarget (X := X) n (q + 1) := by
  have he := exact_tensorRight_rootsOfUnityModule f n
  have := he.1
  have := he.2.1
  have := he.2.2
  exact Stacks.ExtCup.cupHom (𝟙 _) (Nat.add_comm 1 q)

variable (hX : IsUnit (n : Γ(X, ⊤)))

/-- The ordered cup of the original Kummer classes, left-associated in native tensor powers. -/
def orderedKummerCup : (q : ℕ) → (Fin q → unitsModuloPowers X n) →
    rootsOfUnityPowerTarget (X := X) n q
  | 0, _ => Ext.mk₀ (𝟙 _)
  | q + 1, a => rootsOfUnityPowerCupHom f n q
      (orderedKummerCup q (fun i => a i.castSucc))
      (kummerModuleUnitClass n hX (a (Fin.last q)))

/-- The empty ordered symbol is the original unit class. -/
theorem orderedKummerCup_zero (a : Fin 0 → unitsModuloPowers X n) :
    orderedKummerCup f n hX 0 a = Ext.mk₀ (𝟙 _) := rfl

/-- The successor formula retains the original cup and the ordered last coordinate. -/
theorem orderedKummerCup_succ (q : ℕ) (a : Fin (q + 1) → unitsModuloPowers X n) :
    orderedKummerCup f n hX (q + 1) a = rootsOfUnityPowerCupHom f n q
      (orderedKummerCup f n hX q (fun i => a i.castSucc))
      (kummerModuleUnitClass n hX (a (Fin.last q))) := rfl

/-- A zero final Kummer input makes the ordered cup zero. -/
theorem orderedKummerCup_eq_zero_of_last (q : ℕ)
    (a : Fin (q + 1) → unitsModuloPowers X n) (ha : a (Fin.last q) = 0) :
    orderedKummerCup f n hX (q + 1) a = 0 := by
  rw [orderedKummerCup_succ, ha, map_zero, map_zero]

/-- The actual unit quotient, hence its Kummer class, is killed by n. -/
theorem nsmul_kummerModuleUnitClass (a : unitsModuloPowers X n) :
    n • kummerModuleUnitClass n hX a = 0 := by
  rw [← map_nsmul]
  have ha : n • a = 0 := by
    induction a using QuotientAddGroup.induction_on with
    | H a =>
      change n • (QuotientAddGroup.mk' (unitMultiples X n)) a = 0
      rw [← map_nsmul]
      apply (QuotientAddGroup.eq_zero_iff _).mpr
      exact ⟨a, rfl⟩
  rw [ha, map_zero]

/-- Every positive-degree ordered Kummer cup is killed by n. -/
theorem nsmul_orderedKummerCup (q : ℕ)
    (a : Fin (q + 1) → unitsModuloPowers X n) :
    n • orderedKummerCup f n hX (q + 1) a = 0 := by
  rw [orderedKummerCup_succ, ← map_nsmul, nsmul_kummerModuleUnitClass, map_zero]

end Stacks.Kummer
end
