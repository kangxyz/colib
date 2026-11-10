/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Colib.Util.References

/-!
# Exchanging two factors in a relative fourfold product

The literal pullback `(A × B) × (C × D)` is isomorphic to `(C × B) × (A × D)`.
The map exchanges the first and third factors and retains the second and fourth.
It is constructed from native pullback lifts and their universal property. The
coordinate equations specify the actual map, not merely the isomorphism class.
This generic categorical result specializes the original scheme construction.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace CategoryTheory.Limits.pullback

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {S A B D E : C} (a : A ⟶ S) (b : B ⟶ S) (d : D ⟶ S) (e : E ⟶ S)

/-- The literal relative product of two relative products. -/
abbrev fourfold := pullback (pullback.fst a b ≫ a) (pullback.fst d e ≫ d)

/-- The original first-coordinate projection of the relative fourfold product. -/
abbrev fourfoldFirst : fourfold a b d e ⟶ A :=
  pullback.fst _ _ ≫ pullback.fst a b

/-- The original second-coordinate projection of the relative fourfold product. -/
abbrev fourfoldSecond : fourfold a b d e ⟶ B :=
  pullback.fst _ _ ≫ pullback.snd a b

/-- The original third-coordinate projection of the relative fourfold product. -/
abbrev fourfoldThird : fourfold a b d e ⟶ D :=
  pullback.snd _ _ ≫ pullback.fst d e

/-- The original fourth-coordinate projection of the relative fourfold product. -/
abbrev fourfoldFourth : fourfold a b d e ⟶ E :=
  pullback.snd _ _ ≫ pullback.snd d e

/-- The first and second coordinate projections have the same map to the base. -/
theorem fourfoldFirst_base_second :
    fourfoldFirst a b d e ≫ a = fourfoldSecond a b d e ≫ b := by
  simp only [fourfoldFirst, fourfoldSecond, Category.assoc, pullback.condition]

/-- The first and third coordinate projections have the same map to the base. -/
theorem fourfoldFirst_base_third :
    fourfoldFirst a b d e ≫ a = fourfoldThird a b d e ≫ d := by
  simpa only [fourfoldFirst, fourfoldThird, Category.assoc] using
    (pullback.condition (f := pullback.fst a b ≫ a) (g := pullback.fst d e ≫ d))

/-- The first and fourth coordinate projections have the same map to the base. -/
theorem fourfoldFirst_base_fourth :
    fourfoldFirst a b d e ≫ a = fourfoldFourth a b d e ≫ e := by
  rw [fourfoldFirst_base_third]
  simp only [fourfoldThird, fourfoldFourth, Category.assoc, pullback.condition]

/-- Maps into the relative fourfold product are determined by the four original projections. -/
@[ext]
theorem fourfold_hom_ext {W : C} {f g : W ⟶ fourfold a b d e}
    (h₁ : f ≫ fourfoldFirst a b d e = g ≫ fourfoldFirst a b d e)
    (h₂ : f ≫ fourfoldSecond a b d e = g ≫ fourfoldSecond a b d e)
    (h₃ : f ≫ fourfoldThird a b d e = g ≫ fourfoldThird a b d e)
    (h₄ : f ≫ fourfoldFourth a b d e = g ≫ fourfoldFourth a b d e) : f = g := by
  apply pullback.hom_ext
  · exact pullback.hom_ext (by simpa only [fourfoldFirst, Category.assoc] using h₁)
      (by simpa only [fourfoldSecond, Category.assoc] using h₂)
  · exact pullback.hom_ext (by simpa only [fourfoldThird, Category.assoc] using h₃)
      (by simpa only [fourfoldFourth, Category.assoc] using h₄)

/-- Exchange the first and third factors, keeping both remaining coordinates fixed. -/
def fourfoldSwap : fourfold a b d e ⟶ fourfold d b a e :=
  pullback.lift
    (pullback.lift (fourfoldThird a b d e) (fourfoldSecond a b d e)
      ((fourfoldFirst_base_third a b d e).symm.trans (fourfoldFirst_base_second a b d e)))
    (pullback.lift (fourfoldFirst a b d e) (fourfoldFourth a b d e)
      (fourfoldFirst_base_fourth a b d e))
    (by
      simp only [pullback.lift_fst_assoc]
      exact (fourfoldFirst_base_third a b d e).symm)

/-- The first coordinate after exchange is the original third coordinate. -/
@[reassoc (attr := simp)]
theorem fourfoldSwap_first :
    fourfoldSwap a b d e ≫ fourfoldFirst d b a e = fourfoldThird a b d e := by
  simp only [fourfoldSwap, fourfoldFirst, pullback.lift_fst_assoc, pullback.lift_fst]

/-- Exchange preserves the original second coordinate. -/
@[reassoc (attr := simp)]
theorem fourfoldSwap_second :
    fourfoldSwap a b d e ≫ fourfoldSecond d b a e = fourfoldSecond a b d e := by
  simp only [fourfoldSwap, fourfoldSecond, pullback.lift_fst_assoc, pullback.lift_snd]

/-- The third coordinate after exchange is the original first coordinate. -/
@[reassoc (attr := simp)]
theorem fourfoldSwap_third :
    fourfoldSwap a b d e ≫ fourfoldThird d b a e = fourfoldFirst a b d e := by
  simp only [fourfoldSwap, fourfoldThird, pullback.lift_snd_assoc, pullback.lift_fst]

/-- Exchange preserves the original fourth coordinate. -/
@[reassoc (attr := simp)]
theorem fourfoldSwap_fourth :
    fourfoldSwap a b d e ≫ fourfoldFourth d b a e = fourfoldFourth a b d e := by
  simp only [fourfoldSwap, fourfoldFourth, pullback.lift_snd_assoc, pullback.lift_snd]

/-- Exchanging the first and third coordinates twice is the identity. -/
@[simp]
theorem fourfoldSwap_comp : fourfoldSwap a b d e ≫ fourfoldSwap d b a e = 𝟙 _ := by
  apply fourfold_hom_ext <;> simp

/-- The relative partial factor exchange is an involutive isomorphism. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Graph/ProductTransversality.lean:70-118"
  "adaptation" "The actual first/third factor exchange, generalized from schemes to \
    categories with pullbacks"]
def fourfoldSwapIso : fourfold a b d e ≅ fourfold d b a e where
  hom := fourfoldSwap a b d e
  inv := fourfoldSwap d b a e
  hom_inv_id := fourfoldSwap_comp a b d e
  inv_hom_id := fourfoldSwap_comp d b a e

/-- Swapping the first coordinates of a product with itself fixes its entire diagonal. -/
@[reassoc (attr := simp)]
theorem diagonal_fourfoldSwap :
    pullback.diagonal (pullback.fst a b ≫ a) ≫ fourfoldSwap a b a b =
      pullback.diagonal (pullback.fst a b ≫ a) := by
  apply fourfold_hom_ext <;>
    simp only [Category.assoc, fourfoldSwap_first, fourfoldSwap_second,
      fourfoldSwap_third, fourfoldSwap_fourth, fourfoldFirst, fourfoldSecond,
      fourfoldThird, fourfoldFourth, pullback.diagonal_fst_assoc,
      pullback.diagonal_snd_assoc]

end CategoryTheory.Limits.pullback
