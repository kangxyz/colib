/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.LocalRing.Length

/-!
# Literal scalar restriction along a local map with unchanged residue field

Native local length restriction applies to every module, including infinite
length. Surjectivity is required only for the residue map, not for the original
local ring map. This is used for a flat ambient projection along a closed section.
-/

@[expose] public noncomputable section

universe u

namespace ModuleCat

/-- Unchanged residue fields preserve length under the literal local scalar restriction. -/
theorem length_restrictScalars_of_residue_surjective
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    (hf : Function.Surjective (IsLocalRing.ResidueField.map f)) (M : ModuleCat S) :
    Module.length R ((ModuleCat.restrictScalars f).obj M) = Module.length S M := by
  let := f.toAlgebra
  let : IsScalarTower R S ((ModuleCat.restrictScalars f).obj M) := ⟨fun r s x => by
    change (f r * s) • x = f r • (s • x)
    exact mul_smul (f r) s x⟩
  rw [IsLocalRing.length_restrictScalars R S ((ModuleCat.restrictScalars f).obj M)]
  have hres : Module.length (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) = 1 :=
    (Module.length_eq_of_surjective hf).trans (by simp)
  rw [hres, mul_one]
  rfl

end ModuleCat
