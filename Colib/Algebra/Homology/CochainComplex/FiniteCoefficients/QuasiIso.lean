/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Original finite coefficients preserve quasi-isomorphisms -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace CochainComplex.finiteCoefficients

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual map of multiplication cones preserves quasi-isomorphisms at every level. -/
theorem quasiIso_map (n : ℕ) {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (map n f) := by
  let := HasDerivedCategory.standard C
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp
  let t := DerivedCategory.Q.mapTriangle.map
    (mappingCone.triangleMap (n • 𝟙 K) (n • 𝟙 L) f f (by simp))
  have h₁ : IsIso t.hom₁ := by
    change IsIso (DerivedCategory.Q.map f)
    infer_instance
  have h₂ : IsIso t.hom₂ := by
    change IsIso (DerivedCategory.Q.map f)
    infer_instance
  exact isIso₃_of_isIso₁₂ t (DerivedCategory.mappingCone_triangle_distinguished _)
    (DerivedCategory.mappingCone_triangle_distinguished _) h₁ h₂

end CochainComplex.finiteCoefficients
