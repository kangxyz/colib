/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.Data.Finset.Insert
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Finite

/-!
# A common finite scheme-theoretic image

A nonempty finite family of schemes finite over a base has a common closed image
in any separated, locally finite-type scheme over that base. The source is a
finite binary coproduct and the closed scheme is its native `Scheme.Hom.image`.
Every original map factors through it as a morphism of schemes.

The finite projection follows directly from Mathlib's local finite-image theorem
(Stacks, Tag 0AH8) and target-locality of finite morphisms. This lower module does
not import a cycle or correspondence construction. It does not reduce any source
or support, and it adds no flatness, reducedness or integrality hypothesis.

Adapted from `kangxyz/motivic` revision
`a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Morphisms/Finite/CommonImage.lean`
(blob `82f398ab118ad2a5fb32b3af961a522fabcfb2e1`).
The original separate image-projection helper is replaced by direct native use.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

variable {ι : Type v} {X Z : Scheme.{u}}
  (D : ι → Scheme.{u}) (f : ∀ i, D i ⟶ Z) (p : Z ⟶ X)

/-- A finite binary coproduct gives a source finite over the base through which
every selected map factors. The finite family is explicitly nonempty. -/
theorem exists_finite_common_source (s : Finset ι) (hs : s.Nonempty)
    (hf : ∀ i ∈ s, IsFinite (f i ≫ p)) :
    ∃ (W : Scheme.{u}) (a : W ⟶ Z), IsFinite (a ≫ p) ∧
      ∀ i ∈ s, ∃ e : D i ⟶ W, e ≫ a = f i := by
  classical
  revert hf
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
    intro hf
    refine ⟨D i, f i, hf i (Finset.mem_singleton_self i), ?_⟩
    intro j hj
    obtain rfl := Finset.mem_singleton.mp hj
    exact ⟨𝟙 _, Category.id_comp _⟩
  | cons i s hi hs ih =>
    intro hf
    obtain ⟨W, a, ha, he⟩ := ih (fun j hj ↦ hf j (Finset.mem_cons_of_mem hj))
    let : IsFinite (a ≫ p) := ha
    let : IsFinite (f i ≫ p) := hf i (Finset.mem_cons_self i s)
    have hfinite : IsFinite (coprod.desc (f i) a ≫ p) := by
      rw [coprod.desc_comp]
      infer_instance
    refine ⟨D i ⨿ W, coprod.desc (f i) a, hfinite, ?_⟩
    intro j hj
    rcases Finset.mem_cons.mp hj with hji | hj
    · subst j
      exact ⟨coprod.inl, coprod.inl_desc _ _⟩
    · obtain ⟨e, he⟩ := he j hj
      exact ⟨e ≫ coprod.inr, by simpa only [Category.assoc, coprod.inr_desc] using he⟩

/-- The scheme-theoretic image of the common source is a closed scheme finite
over the base, retaining literal factorizations of all selected maps. -/
@[stacks 0AH8 "the local finite-image theorem supplies finiteness of the common image projection"]
theorem exists_finite_common_closed_image [IsSeparated p] [LocallyOfFiniteType p]
    (s : Finset ι) (hs : s.Nonempty) (hf : ∀ i ∈ s, IsFinite (f i ≫ p)) :
    ∃ (C : Scheme.{u}) (j : C ⟶ Z), IsClosedImmersion j ∧ IsFinite (j ≫ p) ∧
      ∀ i ∈ s, ∃ r : D i ⟶ C, r ≫ j = f i := by
  obtain ⟨W, a, ha, he⟩ := exists_finite_common_source D f p s hs hf
  let : IsFinite (a ≫ p) := ha
  let : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
    isZariskiLocalAtTarget_isFinite
  have hfinite : IsFinite (a.imageι ≫ p) := by
    apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
      (P := @IsFinite.{u}) (f := a.imageι ≫ p)
    intro x
    exact exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage a p x
      (((a ≫ p).finite_preimage_singleton x).image a)
  refine ⟨a.image, a.imageι, inferInstance, hfinite, ?_⟩
  intro i hi
  obtain ⟨e, he⟩ := he i hi
  exact ⟨e ≫ a.toImage, by simpa only [Category.assoc, Scheme.Hom.toImage_imageι] using he⟩

end AlgebraicGeometry
