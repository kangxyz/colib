/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOrderedPowers
public import Colib.CategoryTheory.Monoidal.TensorPowProduct
public import Colib.CategoryTheory.Abelian.ExtCupProductPairing
public import Colib.CategoryTheory.Abelian.ExtCupUnit

/-! # Native cup products between ordered Kummer powers -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry MonoidalCategory
universe u
set_option maxRecDepth 4096
attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.EtaleCohomology.isMonoidal_W_etaleModules
namespace Stacks.Kummer
variable {X : Scheme.{u}} {k : Type u} [Field k]
  (f : X ⟶ Spec (.of k)) (n : ℕ) [NeZero n] [NeZero (n : k)]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The ordinary cup product with the native concatenation map of tensor powers. -/
def rootsOfUnityPowerProductHom (p q : ℕ) :
    rootsOfUnityPowerTarget (X := X) n p →+
      rootsOfUnityPowerTarget (X := X) n q →+
        rootsOfUnityPowerTarget (X := X) n (p + q) := by
  have ht := exact_tensorRight_rootsOfUnityModule f n
  have := ht.1
  have := ht.2.1
  have := ht.2.2
  have hp := exact_tensorRight_tensorPow (rootsOfUnityModule.{u, 0} X n) q
  have := hp.1
  have := hp.2.1
  have := hp.2.2
  exact Stacks.ExtCup.cupHom
    (tensorPowAddHom (rootsOfUnityModule.{u, 0} X n) p q) (Nat.add_comm q p)

omit [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- Appending a final degree-one class commutes with the native tensor-power product. -/
theorem rootsOfUnityPowerProductHom_succ (p q : ℕ)
    (a : rootsOfUnityPowerTarget (X := X) n p)
    (b : rootsOfUnityPowerTarget (X := X) n q)
    (c : Ext.{u + 1} (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))))
      (rootsOfUnityModule.{u, 0} X n) 1) :
    rootsOfUnityPowerProductHom f n p (q + 1) a (rootsOfUnityPowerCupHom f n q b c) =
      rootsOfUnityPowerCupHom f n (p + q) (rootsOfUnityPowerProductHom f n p q a b) c := by
  have ht := exact_tensorRight_rootsOfUnityModule f n
  have := ht.1
  have := ht.2.1
  have := ht.2.2
  have hp := exact_tensorRight_tensorPow (rootsOfUnityModule.{u, 0} X n) q
  have := hp.1
  have := hp.2.1
  have := hp.2.2
  have hs := exact_tensorRight_tensorPow (rootsOfUnityModule.{u, 0} X n) (q + 1)
  have : (MonoidalCategory.tensorRight
      (MonoidalCategory.tensorPow (rootsOfUnityModule.{u, 0} X n) q ⊗
        rootsOfUnityModule.{u, 0} X n)).Additive := hs.1
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight
      (MonoidalCategory.tensorPow (rootsOfUnityModule.{u, 0} X n) q ⊗
        rootsOfUnityModule.{u, 0} X n)) := hs.2.1
  have : PreservesFiniteColimits (MonoidalCategory.tensorRight
      (MonoidalCategory.tensorPow (rootsOfUnityModule.{u, 0} X n) q ⊗
        rootsOfUnityModule.{u, 0} X n)) := hs.2.2
  exact Stacks.ExtCup.cup_assoc_pairing
    (tensorPowAddHom (rootsOfUnityModule.{u, 0} X n) p q) a b c
    (Nat.add_comm q p) (Nat.add_comm 1 q) (Nat.add_comm 1 (p + q))
    (Nat.add_comm (q + 1) p)

/-- A final input can be read as a native snoc tuple without changing its ordered cup. -/
theorem orderedKummerCup_snoc (hX : IsUnit (n : Γ(X, ⊤))) (q : ℕ)
    (a : Fin q → unitsModuloPowers X n) (b : unitsModuloPowers X n) :
    orderedKummerCup f n hX (q + 1) (Fin.snoc a b) =
      rootsOfUnityPowerCupHom f n q (orderedKummerCup f n hX q a)
        (kummerModuleUnitClass n hX b) := by
  simp only [orderedKummerCup_succ, Fin.snoc_castSucc, Fin.snoc_last]

omit [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- The empty right tuple acts by the original monoidal right unit. -/
theorem rootsOfUnityPowerProductHom_zero (p : ℕ)
    (a : rootsOfUnityPowerTarget (X := X) n p) :
    rootsOfUnityPowerProductHom f n p 0 a (Ext.mk₀ (𝟙 _)) = a := by
  have ht := exact_tensorRight_rootsOfUnityModule f n
  have := ht.1
  have := ht.2.1
  have := ht.2.2
  have hp := exact_tensorRight_tensorPow (rootsOfUnityModule.{u, 0} X n) 0
  have : (MonoidalCategory.tensorRight (𝟙_ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ZMod n))))).Additive := hp.1
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight (𝟙_ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ZMod n))))) := hp.2.1
  have : PreservesFiniteColimits (MonoidalCategory.tensorRight (𝟙_ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ZMod n))))) := hp.2.2
  exact Stacks.ExtCup.cup_right_unit a

/-- Ordered concatenation of Kummer inputs is their original native cup product. -/
theorem orderedKummerCup_append (hX : IsUnit (n : Γ(X, ⊤))) (p q : ℕ)
    (a : Fin p → unitsModuloPowers X n) (b : Fin q → unitsModuloPowers X n) :
    orderedKummerCup f n hX (p + q) (Fin.append a b) =
      rootsOfUnityPowerProductHom f n p q
        (orderedKummerCup f n hX p a) (orderedKummerCup f n hX q b) := by
  induction q with
  | zero =>
    have h0 : Fin.append a b = a := by simpa using Fin.append_right_nil a b rfl
    rw [h0, orderedKummerCup_zero]
    exact (rootsOfUnityPowerProductHom_zero f n p _).symm
  | succ q ih =>
    induction b using Fin.snocCases with
    | snoc b z =>
      rw [Fin.append_snoc]
      change orderedKummerCup f n hX ((p + q) + 1) (Fin.snoc (Fin.append a b) z) = _
      rw [orderedKummerCup_snoc, orderedKummerCup_snoc, ih]
      exact (rootsOfUnityPowerProductHom_succ f n p q _ _ _).symm

end Stacks.Kummer
end
