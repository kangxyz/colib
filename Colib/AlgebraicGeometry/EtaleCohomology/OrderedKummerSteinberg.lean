/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.OrderedFieldKummer
public import Colib.CategoryTheory.Abelian.ExtCupAssociativity

/-!
# Adjacent Steinberg relations for the original ordered Kummer cups

The last pair is regrouped by the native coefficient associator. Earlier pairs
are handled inductively in the prefix. The only Steinberg input is the existing
relation for the original degree-two field Kummer pairing.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry MonoidalCategory
universe u
set_option maxRecDepth 4096
attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.EtaleCohomology.isMonoidal_W_etaleModules
  comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace Stacks.Kummer
variable {X : Scheme.{u}} {k : Type u} [Field k]
  (f : X ⟶ Spec (.of k)) (n : ℕ) [NeZero n] [NeZero (n : k)]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- A vanishing last pair remains zero with any preceding ordered Kummer inputs. -/
theorem orderedKummerCup_eq_zero_of_last_pair (hX : IsUnit (n : Γ(X, ⊤))) (q : ℕ)
    (a : Fin (q + 2) → unitsModuloPowers X n)
    (ha : kummerCupModuloPowers f n hX (a (Fin.last q).castSucc)
      (a (Fin.last (q + 1))) = 0) :
    orderedKummerCup f n hX (q + 2) a = 0 := by
  have ht := exact_tensorRight_rootsOfUnityModule f n
  have := ht.1
  have := ht.2.1
  have := ht.2.2
  let := Functor.additive_of_iso
    (tensorRightTensor (rootsOfUnityModule.{u, 0} X n) (rootsOfUnityModule.{u, 0} X n)).symm
  let := preservesFiniteLimits_of_natIso
    (tensorRightTensor (rootsOfUnityModule.{u, 0} X n) (rootsOfUnityModule.{u, 0} X n)).symm
  let := preservesFiniteColimits_of_natIso
    (tensorRightTensor (rootsOfUnityModule.{u, 0} X n) (rootsOfUnityModule.{u, 0} X n)).symm
  have hz (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n)))
      (e : Ext.{u + 1} (𝟙_ _) M q)
      (b c : Ext.{u + 1} (𝟙_ _) (rootsOfUnityModule.{u, 0} X n) 1)
      (hbc : Stacks.ExtCup.cup (𝟙 _) b c (by decide : 1 + 1 = 2) = 0) :
      Stacks.ExtCup.cup (𝟙 _) (Stacks.ExtCup.cup (𝟙 _) e b (Nat.add_comm 1 q)) c
        (by omega : 1 + (q + 1) = q + 2) = 0 := by
    have he := Stacks.ExtCup.cup_assoc_of_eq e b c (Nat.add_comm 1 q)
      (by decide : 1 + 1 = 2) (by omega : 1 + (q + 1) = q + 2)
      (by omega : 2 + q = q + 2)
    rw [hbc, Stacks.ExtCup.cup_zero] at he
    have he' := congrArg (fun z => z.comp
      (Ext.mk₀ (α_ M (rootsOfUnityModule.{u, 0} X n)
        (rootsOfUnityModule.{u, 0} X n)).inv) (Nat.add_zero (q + 2))) he
    simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      Iso.hom_inv_id, Ext.comp_mk₀_id, Ext.zero_comp] using he'
  exact hz (tensorPow (rootsOfUnityModule.{u, 0} X n) q)
    (orderedKummerCup f n hX q (fun i => a i.castSucc.castSucc))
    (kummerModuleUnitClass n hX (a (Fin.last q).castSucc))
    (kummerModuleUnitClass n hX (a (Fin.last (q + 1)))) ha

end Stacks.Kummer

namespace AlgebraicGeometry.EtaleCohomology.MilnorKummer
variable (k : Type u) [Field k] (n : ℕ) [NeZero n] [NeZero (n : k)]
  [HasExt.{u + 1} (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- Appending a field unit is the unchanged original cup operation. -/
theorem orderedFieldKummerCup_succ (q : ℕ) (a : Fin (q + 1) → kˣ) :
    orderedFieldKummerCup k n (q + 1) a =
      Stacks.Kummer.rootsOfUnityPowerCupHom (𝟙 (Spec (.of k))) n q
        (orderedFieldKummerCup k n q (fun i => a i.castSucc))
        (Stacks.Kummer.kummerModuleUnitClass n (fieldKummerInvertibility k n)
          (fieldUnitModuloPowers k n (Additive.ofMul (a (Fin.last q))))) := rfl

/-- The original ordered cup vanishes for every adjacent Steinberg pair of field units. -/
theorem orderedFieldKummerCup_steinberg (q : ℕ) (a : Fin q → kˣ) (i j : Fin q)
    (hij : i.val + 1 = j.val) (ha : (a i : k) + (a j : k) = 1) :
    orderedFieldKummerCup k n q a = 0 := by
  induction q with
  | zero => exact Fin.elim0 i
  | succ q ih =>
    induction i using Fin.lastCases with
    | last =>
      have hj := j.isLt
      simp only [Fin.val_last] at hij
      omega
    | cast i =>
      induction j using Fin.lastCases with
      | cast j =>
        rw [orderedFieldKummerCup_succ]
        have hz := ih (fun t => a t.castSucc) i j hij ha
        rw [hz, map_zero, AddMonoidHom.zero_apply]
      | last =>
        cases q with
        | zero => exact Fin.elim0 i
        | succ q =>
          have hi : i = Fin.last q := by
            apply Fin.ext
            simp only [Fin.val_last, Fin.val_castSucc] at hij ⊢
            omega
          subst i
          apply Stacks.Kummer.orderedKummerCup_eq_zero_of_last_pair
          let x := a (Fin.last q).castSucc
          let y := a (Fin.last (q + 1))
          have hy : (y : k) = 1 - (x : k) := eq_sub_of_add_eq' ha
          have hx : IsUnit (1 - (x : k)) := hy ▸ y.isUnit
          have hu : hx.unit = y := Units.ext (hx.unit_spec.trans hy.symm)
          have h := Stacks.Kummer.kummerCupModuloPowers_steinberg n x hx
          rw [hu] at h
          exact h

end AlgebraicGeometry.EtaleCohomology.MilnorKummer
end
