/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Basic
public import Colib.CategoryTheory.Sites.Simplicial.ReducedHypercohomology
public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-!
# The finite-coefficient Bockstein on reduced hypercohomology

The mod-`n` cone map acts by shifted postcomposition in the actual derived
category of ordinary abelian sheaves. The localization shift comparison and
addition of shifts give the target in degree `p + 1`. Shifted composition
transports the strict cochain square-zero identity to reduced hypercohomology.

This construction uses the original reduced cochains of pointed simplicial
presheaves. The comparison with the `n²` coefficient sequence and invariance
under motivic localization are separate statements.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite
open CochainComplex (finiteCoefficients)

universe d w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (Sheaf J AddCommGrpCat.{w})]
  (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) (n : ℕ)

local notation "Kₙ" => finiteCoefficients K n

/-- The actual mod-`n` Bockstein, natural in the pointed simplicial presheaf. -/
def reducedModBockstein (p : ℤ) :
    reducedHypercohomology C J Kₙ p ⟶ reducedHypercohomology C J Kₙ (p + 1) :=
  let β := ShiftedHom.map
    (finiteCoefficients.modBockstein K n : ShiftedHom Kₙ Kₙ (1 : ℤ)) DerivedCategory.Q
  Functor.whiskerLeft (reducedDerivedChains C J).op
    (preadditiveYoneda.map
      (β⟦p⟧' ≫ (shiftFunctorAdd' _ (1 : ℤ) p (p + 1) (add_comm 1 p)).inv.app _))

/-- The component postcomposes with the cone map through the native shift isomorphisms. -/
theorem reducedModBockstein_app_apply (p : ℤ) (X : PointedSimplicialPresheaf.{w} C)
    (x : (reducedHypercohomology C J Kₙ p).obj (op X)) :
    (reducedModBockstein C J K n p).app (op X) x =
      x ≫ (DerivedCategory.Q.map (finiteCoefficients.modBockstein K n) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app Kₙ)⟦p⟧' ≫
        (shiftFunctorAdd' _ (1 : ℤ) p (p + 1) (add_comm 1 p)).inv.app
          (DerivedCategory.Q.obj Kₙ) := rfl

/-- The two consecutive degree-one Bocksteins compose to zero. -/
theorem reducedModBockstein_comp_eq_zero (p : ℤ) :
    reducedModBockstein C J K n p ≫ reducedModBockstein C J K n (p + 1) = 0 := by
  let β : ShiftedHom Kₙ Kₙ (1 : ℤ) := finiteCoefficients.modBockstein K n
  have hβ : β.comp β (rfl : (1 : ℤ) + 1 = 1 + 1) = 0 := by
    rw [ShiftedHom.comp, ← Category.assoc,
      show β ≫ β⟦(1 : ℤ)⟧' = 0 from finiteCoefficients.modBockstein_comp_shift K n,
      zero_comp]
  let b := β.map DerivedCategory.Q
  have hb : b.comp b (rfl : (1 : ℤ) + 1 = 1 + 1) = 0 := by
    dsimp only [b]
    rw [← ShiftedHom.map_comp, hβ, ShiftedHom.map_zero]
  apply NatTrans.ext
  funext X
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  change ShiftedHom ((reducedDerivedChains C J).obj X.unop) (DerivedCategory.Q.obj Kₙ) p at x
  change (x.comp b (add_comm 1 p)).comp b (add_comm 1 (p + 1)) = 0
  rw [ShiftedHom.comp_assoc x b b (add_comm 1 p) (rfl : (1 : ℤ) + 1 = 1 + 1)
    (show (1 : ℤ) + 1 + p = (p + 1) + 1 by omega), hb, ShiftedHom.comp_zero]

end CategoryTheory.PointedSimplicialPresheaf

attribute [colib_tag "COL-0389"]
  CategoryTheory.PointedSimplicialPresheaf.reducedModBockstein
  CategoryTheory.PointedSimplicialPresheaf.reducedModBockstein_comp_eq_zero
