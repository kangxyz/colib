/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOrderedPowers
public import Colib.AlgebraicGeometry.EtaleCohomology.MilnorKummerTwo

/-!
# Ordered Kummer cups of field units

Apply the original field-unit quotient map to the native ordered Kummer cups.
The initial-pair Steinberg relation is inherited from the existing degree-two
pairing. No arbitrary adjacent-pair relation or all-degree descent is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MonoidalCategory
universe u
set_option maxRecDepth 4096
attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.EtaleCohomology.isMonoidal_W_etaleModules
namespace AlgebraicGeometry.EtaleCohomology.MilnorKummer
variable (k : Type u) [Field k] (n : ℕ) [NeZero (n : k)]

/-- The given invertibility of n in the field, transported to its actual global sections. -/
theorem fieldKummerInvertibility : IsUnit (n : Γ(Spec (.of k), ⊤)) := by
  simpa only [map_natCast] using
    (IsUnit.mk0 (n : k) (NeZero.ne (n : k))).map (Scheme.ΓSpecIso (.of k)).inv.hom

variable [NeZero n]
  [HasExt.{u + 1} (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The ordered cup of field units uses the unchanged global-unit quotient and coefficients. -/
def orderedFieldKummerCup (q : ℕ) (a : Fin q → kˣ) :
    Stacks.Kummer.rootsOfUnityPowerTarget (X := Spec (.of k)) n q :=
  Stacks.Kummer.orderedKummerCup (𝟙 (Spec (.of k))) n (fieldKummerInvertibility k n) q
    (fun i => fieldUnitModuloPowers k n (Additive.ofMul (a i)))

/-- Multiplicativity in each field-unit input is the original cup's coordinate additivity. -/
theorem orderedFieldKummerCup_update_mul (q : ℕ) (a : Fin q → kˣ) (i : Fin q)
    (b c : kˣ) :
    orderedFieldKummerCup k n q (Function.update a i (b * c)) =
      orderedFieldKummerCup k n q (Function.update a i b) +
      orderedFieldKummerCup k n q (Function.update a i c) := by
  classical
  let g : kˣ → Stacks.Kummer.unitsModuloPowers (Spec (.of k)) n :=
    fun x => fieldUnitModuloPowers k n (Additive.ofMul x)
  have hg : g (b * c) = g b + g c := (fieldUnitModuloPowers k n).map_add _ _
  have hu (x : kˣ) :
      (fun j => g (Function.update a i x j)) = Function.update (fun j => g (a j)) i (g x) := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [Function.update, h]
  change Stacks.Kummer.orderedKummerCup _ _ _ _ (fun j => g (Function.update a i (b * c) j)) =
    Stacks.Kummer.orderedKummerCup _ _ _ _ (fun j => g (Function.update a i b j)) +
    Stacks.Kummer.orderedKummerCup _ _ _ _ (fun j => g (Function.update a i c j))
  rw [hu, hu, hu, hg]
  exact Stacks.Kummer.orderedKummerCup_update_add _ _ _ _ _ _ _ _

/-- The existing Steinberg relation for the first two inputs persists after further cups. -/
theorem orderedFieldKummerCup_initial_steinberg (q : ℕ) (a : Fin (q + 2) → kˣ)
    (ha : (a ⟨0, by omega⟩ : k) + (a ⟨1, by omega⟩ : k) = 1) :
    orderedFieldKummerCup k n (q + 2) a = 0 := by
  apply Stacks.Kummer.orderedKummerCup_eq_zero_of_initial_pair
  let x := a ⟨0, by omega⟩
  let y := a ⟨1, by omega⟩
  have hy : (y : k) = 1 - (x : k) := eq_sub_of_add_eq' ha
  have hx : IsUnit (1 - (x : k)) := hy ▸ y.isUnit
  have hu : hx.unit = y := Units.ext (hx.unit_spec.trans hy.symm)
  have h := Stacks.Kummer.kummerCupModuloPowers_steinberg n x hx
  rw [hu] at h
  exact h

end AlgebraicGeometry.EtaleCohomology.MilnorKummer
end
