/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-!
Implementation provenance: adapted from the corresponding
`Quillen/Aglib/Algebra/Homology` file at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Actual homotopies after derived equality denominators

In any abelian category with its original derived category, equality of
original chain maps after localization is realized by an actual chain
homotopy after a genuine post-quasi-isomorphism. Two equalities can be
realized with one common denominator. No K-projectivity hypothesis is used.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

lemma exists_post_quasiIso_homotopy_of_derived_eq
    {K L : CochainComplex C ℤ} (f g : K ⟶ L)
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    ∃ (M : CochainComplex C ℤ) (s : L ⟶ M), QuasiIso s ∧ Nonempty (Homotopy (f ≫ s) (g ≫ s)) := by
  let H := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let e := DerivedCategory.quotientCompQhIso C
  have he : DerivedCategory.Qh.map (H.map f) = DerivedCategory.Qh.map (H.map g) := by
    have hf := NatIso.naturality_2 e f
    have hg := NatIso.naturality_2 e g
    exact hf.symm.trans ((congrArg (fun t => e.hom.app K ≫ t ≫ e.inv.app L) h).trans hg)
  obtain ⟨M, s, hs, heq⟩ := (MorphismProperty.map_eq_iff_postcomp DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ)) (H.map f) (H.map g)).mp he
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  obtain ⟨s, rfl⟩ := H.map_surjective s
  refine ⟨M, s, ?_, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  · exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s).mp hs
  · simpa only [Functor.map_comp] using heq

lemma exists_post_quasiIso_two_homotopies_of_derived_eq
    {K₁ K₂ L : CochainComplex C ℤ} (f₁ g₁ : K₁ ⟶ L) (f₂ g₂ : K₂ ⟶ L)
    (h₁ : DerivedCategory.Q.map f₁ = DerivedCategory.Q.map g₁)
    (h₂ : DerivedCategory.Q.map f₂ = DerivedCategory.Q.map g₂) :
    ∃ (M : CochainComplex C ℤ) (s : L ⟶ M), QuasiIso s ∧
      Nonempty (Homotopy (f₁ ≫ s) (g₁ ≫ s)) ∧ Nonempty (Homotopy (f₂ ≫ s) (g₂ ≫ s)) := by
  obtain ⟨M₁, s₁, hs₁, ⟨H₁⟩⟩ := exists_post_quasiIso_homotopy_of_derived_eq f₁ g₁ h₁
  have he₂ : DerivedCategory.Q.map (f₂ ≫ s₁) = DerivedCategory.Q.map (g₂ ≫ s₁) := by
    simp only [Functor.map_comp, h₂]
  obtain ⟨M₂, s₂, hs₂, ⟨H₂⟩⟩ := exists_post_quasiIso_homotopy_of_derived_eq _ _ he₂
  refine ⟨M₂, s₁ ≫ s₂, inferInstance, ⟨?_⟩, ⟨?_⟩⟩
  · simpa only [Category.assoc] using H₁.compRight s₂
  · simpa only [Category.assoc] using H₂

end CochainComplex
