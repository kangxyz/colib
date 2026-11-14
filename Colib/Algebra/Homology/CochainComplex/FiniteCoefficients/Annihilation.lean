/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Annihilation of finite coefficients by the coefficient level

On the original multiplication cone, the off-diagonal map from the integral
coordinate to the shifted integral summand is the homotopy between
multiplication by the coefficient level and zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

universe d v u

namespace CochainComplex.finiteCoefficients

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- Multiplication by the coefficient level on its actual cone is nullhomotopic. -/
def nsmulIdHomotopy (K : CochainComplex C ℤ) (n : ℕ) :
    Homotopy (n • 𝟙 (finiteCoefficients K n)) 0 := by
  let f : K ⟶ K := n • 𝟙 K
  change Homotopy (n • 𝟙 (mappingCone f)) 0
  exact mappingCone.descHomotopy f _ _ 0 (mappingCone.inl f)
    (by
      have h (L : CochainComplex C ℤ) :
          Cochain.ofHom (n • 𝟙 L) = (n : ℤ) • Cochain.ofHom (𝟙 L) := by
        simpa using Cochain.ofHom_smul (n : ℤ) (𝟙 L)
      simp only [f, Cochain.ofHom_zero, Cochain.comp_zero, δ_zero, zero_add,
        add_zero, h, Cochain.smul_comp, Cochain.comp_smul, Cochain.id_comp, Cochain.comp_id])
    (by simp [f])

end CochainComplex.finiteCoefficients

namespace CochainComplex.finiteCoefficients

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{d} C]

/-- The coefficient level annihilates the identity of the actual finite coefficient object. -/
theorem nsmul_id_derived_eq_zero (K : CochainComplex C ℤ) (n : ℕ) :
    n • 𝟙 (DerivedCategory.Q.obj (finiteCoefficients K n)) = 0 := by
  let L := finiteCoefficients K n
  let Q : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q
  have h : Q.map (n • 𝟙 L) = Q.map (0 : L ⟶ L) :=
    DerivedCategory.Q_map_eq_of_homotopy C (nsmulIdHomotopy K n)
  rw [Q.map_nsmul, Q.map_id, Q.map_zero] at h
  exact h

/-- Derived classes with finite coefficients are annihilated by the coefficient level. -/
theorem nsmul_shiftedHom_eq_zero (K : CochainComplex C ℤ) (n : ℕ)
    {A : DerivedCategory C} {p : ℤ} (x : A ⟶ (DerivedCategory.Q.obj (finiteCoefficients K n))⟦p⟧) :
    n • x = 0 := by
  let L : DerivedCategory C := DerivedCategory.Q.obj (finiteCoefficients K n)
  let S : DerivedCategory C ⥤ DerivedCategory C := CategoryTheory.shiftFunctor _ p
  have h := congrArg (S.map : (L ⟶ L) → _) (nsmul_id_derived_eq_zero K n)
  rw [S.map_nsmul, S.map_id, S.map_zero] at h
  rw [← Category.comp_id x, ← Preadditive.comp_nsmul, h, comp_zero]

end CochainComplex.finiteCoefficients
