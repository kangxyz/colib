/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.ModBockstein
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# The finite-coefficient composition triangle

Apply the native cone-composition triangle to two copies of multiplication
by `n`. Its arrows are the original insertion, reduction and mod-`n`
Bockstein. The sign of the connecting map comes from the same cone triangle
as the integral Bockstein. The construction works at every natural level.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace CochainComplex.finiteCoefficients

section Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  (K : CochainComplex C ℤ) (n : ℕ)

/-- The coefficient triangle from `K/n` through `K/(n*n)` back to `K/n`. -/
def compositionTriangle : Triangle (CochainComplex C ℤ) :=
  Triangle.mk (insertion K n n) (reduction K n n) (modBockstein K n)

@[simp]
theorem compositionTriangle_mor₁ : (compositionTriangle K n).mor₁ = insertion K n n := rfl

@[simp]
theorem compositionTriangle_mor₂ : (compositionTriangle K n).mor₂ = reduction K n n := rfl

@[simp]
theorem compositionTriangle_mor₃ : (compositionTriangle K n).mor₃ = modBockstein K n := rfl

/-- The actual insertion, reduction and Bockstein agree with the native composition triangle. -/
theorem compositionTriangle_eq_mappingConeCompTriangle :
    compositionTriangle K n = mappingConeCompTriangle (n • 𝟙 K) (n • 𝟙 K) := by
  let f : K ⟶ K := n • 𝟙 K
  have hmul : f ≫ f = (n * n) • 𝟙 K := by
    simp only [f, Preadditive.nsmul_comp, Category.id_comp, smul_smul]
  have compare (g : K ⟶ K) (h : f ≫ f = g) :
      Triangle.mk (mappingCone.map f g (𝟙 K) f (by rw [Category.id_comp, h]))
        (mappingCone.map g f f (𝟙 K) (by rw [Category.comp_id, h]))
        ((mappingCone.triangle f).mor₃ ≫ (mappingCone.inr f)⟦(1 : ℤ)⟧') =
      mappingConeCompTriangle f f := by
    subst g
    rfl
  exact compare _ hmul

/-- The finite-coefficient composition triangle is distinguished in the homotopy category. -/
theorem compositionTriangle_distinguished [HasZeroObject C] :
    (HomotopyCategory.quotient C (.up ℤ)).mapTriangle.obj (compositionTriangle K n) ∈
      distTriang (HomotopyCategory C (.up ℤ)) := by
  rw [compositionTriangle_eq_mappingConeCompTriangle]
  exact HomotopyCategory.mappingConeCompTriangleh_distinguished (n • 𝟙 K) (n • 𝟙 K)

end Homotopy

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (K : CochainComplex C ℤ) (n : ℕ)

/-- The actual finite-coefficient composition triangle is distinguished after localization. -/
theorem compositionTriangle_derived_distinguished :
    DerivedCategory.Q.mapTriangle.obj (compositionTriangle K n) ∈
      distTriang (DerivedCategory C) := by
  let T := compositionTriangle K n
  let Q₀ := HomotopyCategory.quotient C (.up ℤ)
  let Qh := DerivedCategory.Qh (C := C)
  let e := (Functor.mapTriangleCompIso Q₀ Qh).symm.app T ≪≫
    (Functor.mapTriangleIso (DerivedCategory.quotientCompQhIso C)).app T
  exact (distinguished_iff_of_iso e).mp
    (Qh.map_distinguished _ (compositionTriangle_distinguished K n))

end Derived

end CochainComplex.finiteCoefficients

namespace CochainComplex.finiteCoefficients

attribute [colib_tag "COL-1018"]
  compositionTriangle
  compositionTriangle_mor₁
  compositionTriangle_mor₂
  compositionTriangle_mor₃
  compositionTriangle_derived_distinguished
  modBockstein_comp_shift

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Algebra/Homology/HomotopyCategory/Triangulated.lean:34-50,193-201"
  "adaptation" "The cone-composition triangle for repeated multiplication by n"]
  compositionTriangle_derived_distinguished

end CochainComplex.finiteCoefficients
