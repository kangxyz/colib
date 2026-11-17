/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.KummerCupProduct
public import StacksFrontier.CategoryTheory.Monoidal.TensorPow
public import Mathlib.LinearAlgebra.Multilinear.Basic

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

/-- The degree-one ordered cup is the original Kummer class after the native unitor. -/
theorem orderedKummerCup_one (a : Fin 1 → unitsModuloPowers X n) :
    (orderedKummerCup f n hX 1 a).comp
        (Ext.mk₀ (λ_ (rootsOfUnityModule.{u, 0} X n)).hom) (by decide : 1 + 0 = 1) =
      kummerModuleUnitClass n hX (a 0) := by
  have he := exact_tensorRight_rootsOfUnityModule f n
  have := he.1
  have := he.2.1
  have := he.2.2
  have hu (b : Ext.{u + 1}
      (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))))
      (rootsOfUnityModule.{u, 0} X n) 1) :
      (Stacks.ExtCup.cup (𝟙 _) (Ext.mk₀ (𝟙 _)) b (by decide : 1 + 0 = 1)).comp
        (Ext.mk₀ (λ_ (rootsOfUnityModule.{u, 0} X n)).hom) (by decide : 1 + 0 = 1) = b := by
    simp [Stacks.ExtCup.cup, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  exact hu (kummerModuleUnitClass n hX (a 0))

/-- Degree two agrees with the existing Kummer pairing, not a new cup product. -/
theorem orderedKummerCup_two (a : Fin 2 → unitsModuloPowers X n) :
    (orderedKummerCup f n hX 2 a).comp
        (Ext.mk₀ ((λ_ (rootsOfUnityModule.{u, 0} X n)).hom ▷
          rootsOfUnityModule.{u, 0} X n)) (by decide : 2 + 0 = 2) =
      kummerCupModuloPowers f n hX (a 0) (a 1) := by
  have he := exact_tensorRight_rootsOfUnityModule f n
  have := he.1
  have := he.2.1
  have := he.2.2
  have hc (e : Ext.{u + 1}
      (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))))
      (𝟙_ _ ⊗ rootsOfUnityModule.{u, 0} X n) 1) :
      (Stacks.ExtCup.cup (𝟙 _) e (kummerModuleUnitClass n hX (a 1))
          (by decide : 1 + 1 = 2)).comp
          (Ext.mk₀ ((λ_ (rootsOfUnityModule.{u, 0} X n)).hom ▷
            rootsOfUnityModule.{u, 0} X n)) (by decide : 2 + 0 = 2) =
        Stacks.ExtCup.cup (𝟙 _)
          (e.comp (Ext.mk₀ (λ_ (rootsOfUnityModule.{u, 0} X n)).hom)
            (by decide : 1 + 0 = 1))
          (kummerModuleUnitClass n hX (a 1)) (by decide : 1 + 1 = 2) := by
    rw [Stacks.ExtCup.cup_comp_mk₀, Category.id_comp,
      Stacks.ExtCup.comp_mk₀_cup, Category.comp_id]
  have hr := hc (orderedKummerCup f n hX 1 (fun i => a i.castSucc))
  exact hr.trans (congrArg
    (fun e => Stacks.ExtCup.cup (𝟙 _) e (kummerModuleUnitClass n hX (a 1))
      (by decide : 1 + 1 = 2))
    (orderedKummerCup_one f n hX (fun i => a i.castSucc)))

/-- Vanishing of the existing degree-two cup implies vanishing before normalization. -/
theorem orderedKummerCup_two_eq_zero (a : Fin 2 → unitsModuloPowers X n)
    (ha : kummerCupModuloPowers f n hX (a 0) (a 1) = 0) :
    orderedKummerCup f n hX 2 a = 0 := by
  have hi (e : Ext.{u + 1}
      (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))))
      ((𝟙_ _ ⊗ rootsOfUnityModule.{u, 0} X n) ⊗ rootsOfUnityModule.{u, 0} X n) 2)
      (he : e.comp (Ext.mk₀ ((λ_ (rootsOfUnityModule.{u, 0} X n)).hom ▷
        rootsOfUnityModule.{u, 0} X n)) (by decide : 2 + 0 = 2) = 0) : e = 0 := by
    have h' := congrArg (fun z => z.comp
      (Ext.mk₀ ((λ_ (rootsOfUnityModule.{u, 0} X n)).inv ▷
        rootsOfUnityModule.{u, 0} X n)) (by decide : 2 + 0 = 2)) he
    simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      ← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight,
      Ext.comp_mk₀_id, Ext.zero_comp] using h'
  exact hi _ ((orderedKummerCup_two f n hX a).trans ha)

/-- An initial vanishing pair remains zero after appending further Kummer classes. -/
theorem orderedKummerCup_eq_zero_of_initial_pair (q : ℕ)
    (a : Fin (q + 2) → unitsModuloPowers X n)
    (ha : kummerCupModuloPowers f n hX (a ⟨0, by omega⟩) (a ⟨1, by omega⟩) = 0) :
    orderedKummerCup f n hX (q + 2) a = 0 := by
  induction q with
  | zero => exact orderedKummerCup_two_eq_zero f n hX a ha
  | succ q ih =>
    rw [orderedKummerCup_succ]
    have hz : orderedKummerCup f n hX (q + 2) (fun i => a i.castSucc) = 0 :=
      ih _ ha
    rw [hz, map_zero, AddMonoidHom.zero_apply]

/-- Additivity in every coordinate of the ordered cup, before Milnor descent. -/
theorem orderedKummerCup_update_add (q : ℕ)
    (a : Fin q → unitsModuloPowers X n) (i : Fin q)
    (b c : unitsModuloPowers X n) :
    orderedKummerCup f n hX q (Function.update a i (b + c)) =
      orderedKummerCup f n hX q (Function.update a i b) +
      orderedKummerCup f n hX q (Function.update a i c) := by
  classical
  induction q with
  | zero => exact Fin.elim0 i
  | succ q ih =>
    induction i using Fin.lastCases with
    | last =>
      simp only [orderedKummerCup_succ, Function.update_self]
      have h (v : unitsModuloPowers X n) :
          (fun j : Fin q => Function.update a (Fin.last q) v j.castSucc) =
            (fun j => a j.castSucc) := by
        funext j
        simp
      simp only [h, map_add]
    | cast i =>
      have h (v : unitsModuloPowers X n) :
          (fun j : Fin q => Function.update a i.castSucc v j.castSucc) =
            Function.update (fun j => a j.castSucc) i v := by
        funext j
        by_cases hij : j = i
        · subst j; simp
        · simp [Function.update, hij]
      simp only [orderedKummerCup_succ, h]
      have hlast (v : unitsModuloPowers X n) :
          Function.update a i.castSucc v (Fin.last q) = a (Fin.last q) := by
        have hne : Fin.last q ≠ i.castSucc := by
          intro hh
          have hv := congrArg Fin.val hh
          simp only [Fin.val_last, Fin.val_castSucc] at hv
          omega
        exact Function.update_of_ne hne v a
      simp only [hlast, ih, map_add, AddMonoidHom.add_apply]

/-- Fixing all but one input gives an additive map of actual unit quotients. -/
def orderedKummerCoordinateHom (q : ℕ)
    (a : Fin q → unitsModuloPowers X n) (i : Fin q) :
    unitsModuloPowers X n →+ rootsOfUnityPowerTarget (X := X) n q :=
  AddMonoidHom.mk' (fun b => orderedKummerCup f n hX q (Function.update a i b))
    (orderedKummerCup_update_add f n hX q a i)

/-- A zero in any coordinate makes a positive-degree ordered cup zero. -/
theorem orderedKummerCup_update_zero (q : ℕ)
    (a : Fin q → unitsModuloPowers X n) (i : Fin q) :
    orderedKummerCup f n hX q (Function.update a i 0) = 0 :=
  (orderedKummerCoordinateHom f n hX q a i).map_zero

/-- The ordered Kummer cup is integer-multilinear in the original unit quotients. -/
@[colib_tag "COL-1299"]
def orderedKummerMultilinear (q : ℕ) :
    MultilinearMap ℤ (fun _ : Fin q => unitsModuloPowers X n)
      (rootsOfUnityPowerTarget (X := X) n q) :=
  MultilinearMap.mk' (orderedKummerCup f n hX q)
    (orderedKummerCup_update_add f n hX q)
    (fun a i z b => (orderedKummerCoordinateHom f n hX q a i).map_zsmul z b)

/-- Multilinear packaging leaves the original ordered cup values unchanged. -/
theorem orderedKummerMultilinear_apply (q : ℕ)
    (a : Fin q → unitsModuloPowers X n) :
    orderedKummerMultilinear f n hX q a = orderedKummerCup f n hX q a := rfl

end Stacks.Kummer
end
