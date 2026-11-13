/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.CohomologySequence
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The ordinary Kummer map on global units modulo powers

This file consumes the actual small-étale Kummer boundary and degree-zero sheaf cohomology.
The target is ordinary `Sheaf.H`, not motivic cohomology. No trivialization of roots of unity
and no primitive root choice is used. The map is injective for every scheme with the stated
invertibility hypothesis; surjectivity and higher cup symbols are not asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w u v

namespace Stacks.Kummer


variable (X : Scheme.{u})
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- Global units, written additively, are the actual degree-zero cohomology of `𝐆_m`. -/
def globalUnitsH0Equiv : Additive (Γ(X, ⊤))ˣ ≃+
    Sheaf.H.{w} (multiplicativeSheaf.{u, v} X) 0 := by
  let : MorphismProperty.ContainsIdentities (@Etale.{u}) := ⟨fun _ => inferInstance⟩
  let hT : IsTerminal (Scheme.Etale.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal _ _
  let e := Sheaf.H.equiv₀.{w} (multiplicativeSheaf.{u, v} X) hT
  exact
    { toFun := fun a => e.symm (ULift.up a)
      invFun := fun x => (e x).down
      left_inv := fun a => congrArg ULift.down (e.apply_symm_apply (ULift.up a))
      right_inv := fun x => by
        apply e.injective
        change e (e.symm (e x)) = e x
        exact e.apply_symm_apply _
      map_add' := fun a b => e.symm.map_add _ _ }

variable {n : ℕ} (hn0 : n ≠ 0) (hX : IsUnit (n : Γ(X, ⊤)))

/-- The ordinary Kummer class of a global unit, using the original boundary. -/
def unitKummerClass : Additive (Γ(X, ⊤))ˣ →+
    Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) 1 :=
  (kummerδ X hn0 hX 0).comp (globalUnitsH0Equiv.{w, u, v} X).toAddMonoidHom

/-- The subgroup of powers, read additively as the range of multiplication by `n`. -/
def unitMultiples (n : ℕ) : AddSubgroup (Additive (Γ(X, ⊤))ˣ) :=
  (n • AddMonoidHom.id (Additive (Γ(X, ⊤))ˣ)).range

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] in
/-- Membership means being an actual `n`-th power of a global unit. -/
theorem mem_unitMultiples_iff (a : (Γ(X, ⊤))ˣ) :
    Additive.ofMul a ∈ unitMultiples X n ↔ ∃ b : (Γ(X, ⊤))ˣ, b ^ n = a := by
  change (∃ b : Additive (Γ(X, ⊤))ˣ, n • b = Additive.ofMul a) ↔ _
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.toMul, congrArg Additive.toMul hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩

/-- A global unit has zero Kummer class exactly when it is a power. -/
theorem unitKummerClass_eq_zero_iff (a : Additive (Γ(X, ⊤))ˣ) :
    unitKummerClass X hn0 hX a = 0 ↔ ∃ b, n • b = a := by
  change kummerδ X hn0 hX 0 (globalUnitsH0Equiv X a) = 0 ↔ _
  rw [← mem_range_sheafH_map_powMap_iff.{w, u, v} X hn0 hX 0]
  change (∃ y, Sheaf.H.map (powMap.{u, v} X n) 0 y = globalUnitsH0Equiv X a) ↔ _
  simp only [sheafH_map_powMap]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(globalUnitsH0Equiv X).symm y, (globalUnitsH0Equiv X).injective ?_⟩
    simpa only [map_nsmul, AddEquiv.apply_symm_apply] using hy
  · rintro ⟨b, rfl⟩
    exact ⟨globalUnitsH0Equiv X b, (map_nsmul (globalUnitsH0Equiv X) n b).symm⟩

/-- The exact kernel of the original unit Kummer class. -/
theorem unitKummerClass_ker : (unitKummerClass X hn0 hX).ker = unitMultiples X n := by
  ext a
  exact unitKummerClass_eq_zero_iff X hn0 hX a

/-- The Kummer class vanishes precisely on actual powers of global units. -/
theorem unitKummerClass_ofMul_eq_zero_iff (a : (Γ(X, ⊤))ˣ) :
    unitKummerClass X hn0 hX (Additive.ofMul a) = 0 ↔
      ∃ b : (Γ(X, ⊤))ˣ, b ^ n = a := by
  rw [← AddMonoidHom.mem_ker, unitKummerClass_ker, mem_unitMultiples_iff]

/-- Global units modulo powers, with the original group quotient. -/
abbrev unitsModuloPowers (n : ℕ) := Additive (Γ(X, ⊤))ˣ ⧸ unitMultiples X n

/-- The ordinary Kummer map from global units modulo powers to actual étale `H¹(μ_n)`. -/
def kummerClassModuloPowers : unitsModuloPowers X n →+
    Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) 1 :=
  QuotientAddGroup.lift (unitMultiples X n) (unitKummerClass X hn0 hX)
    (le_of_eq (unitKummerClass_ker X hn0 hX).symm)

/-- The quotient map is the original boundary on each global unit. -/
theorem kummerClassModuloPowers_mk (a : Additive (Γ(X, ⊤))ˣ) :
    kummerClassModuloPowers X hn0 hX (QuotientAddGroup.mk a) = unitKummerClass X hn0 hX a := rfl

/-- Global units modulo powers inject into ordinary degree-one étale cohomology. -/
@[colib_tag "COL-1227", stacks 03PL
  "Injective global-unit power quotient from the ordinary Kummer sequence"]
theorem kummerClassModuloPowers_injective :
    Function.Injective (kummerClassModuloPowers X hn0 hX) := by
  apply (QuotientAddGroup.injective_lift_iff _ _ _).2
  exact (unitKummerClass_ker X hn0 hX).symm

end Stacks.Kummer
