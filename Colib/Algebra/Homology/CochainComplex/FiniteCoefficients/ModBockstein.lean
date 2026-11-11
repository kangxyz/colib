/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Basic

/-!
# The mod-n Bockstein of the coefficient cone

The positive connecting map of the multiplication cone, followed by shifted
integral reduction, acts on the same finite coefficient complex with degree
one. Its shifted square vanishes on cochains.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.finiteCoefficients

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  (K : CochainComplex C ℤ) (n : ℕ)

/-- Integral reduction followed by the positive connecting map is zero on cochains. -/
@[reassoc (attr := simp)]
theorem integral_bockstein : integral K n ≫ bockstein K n = 0 :=
  mappingCone.inr_triangleδ (n • 𝟙 K)

/-- Reduce the positive integral connecting map to the same finite coefficient level. -/
noncomputable def modBockstein : finiteCoefficients K n ⟶ (finiteCoefficients K n)⟦(1 : ℤ)⟧ :=
  bockstein K n ≫ (integral K n)⟦(1 : ℤ)⟧'

/-- The mod-`n` Bockstein followed by its shift is zero. -/
@[reassoc]
theorem modBockstein_comp_shift :
    modBockstein K n ≫ (modBockstein K n)⟦(1 : ℤ)⟧' = 0 := by
  have h : (integral K n)⟦(1 : ℤ)⟧' ≫ (bockstein K n)⟦(1 : ℤ)⟧' = 0 := by
    rw [← Functor.map_comp, integral_bockstein, Functor.map_zero]
  simp only [modBockstein, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((integral K n)⟦(1 : ℤ)⟧'), h, zero_comp, comp_zero]

variable {K} {L : CochainComplex C ℤ}

/-- The mod-`n` Bockstein is natural in the original integral complex. -/
@[reassoc]
theorem modBockstein_naturality (f : K ⟶ L) :
    map n f ≫ modBockstein L n = modBockstein K n ≫ (map n f)⟦(1 : ℤ)⟧' := by
  calc
    _ = bockstein K n ≫ (f ≫ integral L n)⟦(1 : ℤ)⟧' := by
      rw [modBockstein, ← Category.assoc, bockstein_naturality, Category.assoc, Functor.map_comp]
    _ = _ := by
      rw [← integral_naturality, Functor.map_comp, modBockstein, Category.assoc]

end CochainComplex.finiteCoefficients
